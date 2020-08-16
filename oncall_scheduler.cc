#include "absl/strings/str_cat.h"

#include "ortools/base/commandlineflags.h"
#include "ortools/base/integral_types.h"
#include "ortools/base/logging.h"
#include "ortools/sat/cp_model.h"

#include <algorithm>
#include <vector>
#include <random>

using operations_research::Domain;

using operations_research::sat::BoolVar;
using operations_research::sat::CpModelBuilder;
using operations_research::sat::IntVar;
using operations_research::sat::LinearExpr;
using operations_research::sat::Model;
using operations_research::sat::SolveCpModel;
using operations_research::sat::CpSolverResponse;
using operations_research::sat::CpSolverResponseStats;

DEFINE_int32(num_weeks, 4, "Number of weeks to look forward");

namespace oncall_scheduler {


// The carbon based life form part of the oncall rotation consisting
// of a name and location.
struct Person {
    std::string name;
    std::string location_name;
};

// The actual oncall rotation (e.g. with schedule times per location).
struct Rotation {
    std::vector<Person> persons;
};

// TODO(freyth): Consult the proto of previous oncalls
static bool was_primary_oncall(int week, Person p) {
    return p.name == "me";
}

static bool was_secondary_oncall(int week, Person p) {
    return p.name == "be";
}

enum dir {
        Lhs,
        Rhs,
};

// Apply a (soft) constraint to either the left or the rhs.
// TODO(zecke): We don't actually need the dir here? do we?
static void AddSoftLessOrEqual(LinearExpr *objective, CpModelBuilder *builder,
                                const Domain& domain, enum dir dir,
                                LinearExpr left, LinearExpr right) {
    IntVar surplus = builder->NewIntVar(domain);
    IntVar deficit = builder->NewIntVar(domain);

    switch (dir) {
    case Lhs:
        left.AddVar(surplus);
        left.AddTerm(deficit, -1);
        break;
    case Rhs:
        right.AddVar(surplus);
        right.AddTerm(deficit, -1);
        break;
    }

    objective->AddVar(surplus);
    objective->AddVar(deficit);

    builder->AddLessOrEqual(left, right);
}

// Remove persons that are completely out of office.
std::vector<Person> filterOOO(int num_shifts, const std::vector<Person>& person) {
    // TODO(zecke): Embrace c++20 when it's available
    std::vector<Person> available(person.size());
    auto it = std::copy_if(person.begin(), person.end(), available.begin(),
                 [](const Person& p) {
                    return p.name != "ooo";
                 });
    available.resize(std::distance(available.begin(), it));
    return available;
}

// Schedules #`shifts` considering `lookback` number of previous shifts.
void schedule(const int num_shifts, const int lookback) {
    const auto rotation = Rotation{
            .persons = std::vector<Person>{
                    Person{"me", "abc"},
                    Person{"be", "abc"},
                    Person{"ce", "def"},
                    Person{"fe", "def"},
                    Person{"ooo", "def"},
            },
    };

    CpModelBuilder builder;

    // Get the people that can handle at least one shift and randomize
    // to avoid always selecting one person first.
    auto availablePersons = filterOOO(num_shifts, rotation.persons);
    std::random_device rd;
    std::mt19937 g(rd());
    std::shuffle(availablePersons.begin(), availablePersons.end(), g);


    std::vector<std::vector<BoolVar>> primary_shifts(lookback + num_shifts);
    std::vector<std::vector<BoolVar>> secondary_shifts(lookback + num_shifts);

    // Look back to previous and already scheduled shifts and add the truths.
    for (int i = 0; i < lookback; ++i) {
            primary_shifts[i].resize(availablePersons.size());
            secondary_shifts[i].resize(availablePersons.size());

            for (int p_no = 0; p_no < availablePersons.size(); ++p_no) {
                const Person& p = availablePersons[p_no];
                BoolVar p_shift, s_shift;

                if (was_primary_oncall(i, p)) {
                        p_shift = builder.TrueVar();
                } else {
                        p_shift = builder.FalseVar();
                }

                if (was_secondary_oncall(i, p)) {
                        s_shift = builder.TrueVar();
                } else {
                        s_shift = builder.FalseVar();
                }

                p_shift = p_shift.WithName(absl::StrCat("past_p_shift_", i, "_", p.name));
                s_shift = s_shift.WithName(absl::StrCat("past_s_shift_", i, "_", p.name));
                primary_shifts[i][p_no] = p_shift;
                secondary_shifts[i][p_no] = s_shift;
            }
    }

    // Create the shifts we need to schedule.
    for (int i = 0; i < num_shifts; ++i) {
            const int shift = i + lookback;
            primary_shifts[shift].resize(availablePersons.size());
            secondary_shifts[shift].resize(availablePersons.size());

            for (int p_no = 0; p_no < availablePersons.size(); ++p_no) {
                const Person& p = availablePersons[p_no];
                auto p_shift = builder.NewBoolVar()
                                    .WithName(absl::StrCat("p_shift_", shift, "_", p.name));
                auto s_shift = builder.NewBoolVar()
                                    .WithName(absl::StrCat("s_shift_", shift, "_", p.name));
                primary_shifts[shift][p_no] = p_shift;
                secondary_shifts[shift][p_no] = s_shift;

                // Person must not be primary and secondary at the same time.
                builder.AddLessOrEqual(LinearExpr::BooleanSum({p_shift, s_shift}), 1);

                // We will not be primary or secondary back to back.
                if (shift >= 1) {
                        const BoolVar& previous_p_shift = primary_shifts[shift - 1][p_no];
                        const auto p_sum = LinearExpr::BooleanSum({p_shift, previous_p_shift});
                        builder.AddLessOrEqual(p_sum, 1);

                        const BoolVar& previous_s_shift = secondary_shifts[shift - 1][p_no];
                        const auto s_sum = LinearExpr::BooleanSum({s_shift, previous_s_shift});
                        builder.AddLessOrEqual(s_sum, 1);
                }
            }

            // Each shift must have a person assigned.
            builder.AddEquality(LinearExpr::BooleanSum(primary_shifts[shift]), 1);
            builder.AddEquality(LinearExpr::BooleanSum(secondary_shifts[shift]), 1);
    }

    // Make sure everyone has an equal number of assignments. Make these
    // constraints soft as with OOO scheduling some people might need to
    // take more shifts than others.
    const int total_shifts = num_shifts + lookback;
    const int min_shifts = (total_shifts) / availablePersons.size();
    const int max_shifts = ((total_shifts) % availablePersons.size()) == 0 ? (min_shifts) : min_shifts + 1;
    LOG(INFO) << "min: " << min_shifts << " max: " << max_shifts;

    LinearExpr objective;

    for (int p_no = 0; p_no < availablePersons.size(); ++p_no) {
            std::vector<BoolVar> p_person_shifts, s_person_shifts;

            for (const std::vector<BoolVar>& shifts : primary_shifts) {
                    p_person_shifts.push_back(shifts[p_no]);
            }
            for (const std::vector<BoolVar>& shifts : secondary_shifts) {
                    s_person_shifts.push_back(shifts[p_no]);
            }

            // Assign equal number of primary shifts. Turn this into a soft
            // constraint
            AddSoftLessOrEqual(&objective, &builder, Domain(0, min_shifts), Rhs,
                               min_shifts, LinearExpr::BooleanSum(p_person_shifts));
            AddSoftLessOrEqual(&objective, &builder, Domain(0, max_shifts * 2), Lhs,
                               LinearExpr::BooleanSum(p_person_shifts), max_shifts);

            AddSoftLessOrEqual(&objective, &builder, Domain(0, min_shifts), Rhs,
                               min_shifts, LinearExpr::BooleanSum(s_person_shifts));
            AddSoftLessOrEqual(&objective, &builder, Domain(0, max_shifts * 2), Lhs,
                                LinearExpr::BooleanSum(s_person_shifts), max_shifts);
    }


    // TODO(zecke): Honor OOO, public holidays or other shifts. We might need to do
    // this in two places.
    // 1.) E.g. OOO or other shift should be a hard FalseVar
    // 2.) public holiday should be a penalty...

    // Some hacks to simulate...
    // Make "me" take all weeks OOO but the first one. This should violate the
    // min_shifts constraint.
    for (int i = 1; i < num_shifts; ++i) {
        builder.AddEquality(primary_shifts[lookback+i][0], builder.FalseVar());
        builder.AddEquality(secondary_shifts[lookback+i][0], builder.FalseVar());
    }

    // Simulate a public holiday in DEF which makes scheduling more expensive.
    for (int i = 0; i < num_shifts; ++i) {
            const int shift = lookback + i;

            for (int p_no = 0; p_no < availablePersons.size(); ++p_no) {
                    const Person& person = availablePersons[p_no];

                    int cost = 1;
                    if (person.location_name == "def" && i > 3 && i < 5) {
                        cost = 10;
                    }
                    objective.AddTerm(primary_shifts[shift][p_no], cost);
                    objective.AddTerm(secondary_shifts[shift][p_no], cost);
            }
    }

    builder.Minimize(objective);

    // TODO(zecke): Optimize for space between two primary shifts..


    Model model;
    const CpSolverResponse response = SolveCpModel(builder.Build(), &model);
    LOG(INFO) << CpSolverResponseStats(response);


    for (int i = 0; i < num_shifts; ++i) {
        int shift = i + lookback;

        for (int p = 0; p < availablePersons.size(); ++p) {
            const Person person = availablePersons[p];

            if (SolutionBooleanValue(response, primary_shifts[shift][p])) {
                    LOG(INFO) << "Primary Shift #" << shift << " for: " << person.name;
            }
        }
    }

    for (int i = 0; i < num_shifts; ++i) {
        int shift = i + lookback;

        for (int p = 0; p < availablePersons.size(); ++p) {
            const Person person = availablePersons[p];

            if (SolutionBooleanValue(response, secondary_shifts[shift][p])) {
                    LOG(INFO) << "Secondary Shift #" << shift << " for: " << person.name;
            }
        }
    }
}
}

static const char kUsage[] =
    "Usage: see flags.\n";

int main(int argc, char **argv) {
  gflags::SetUsageMessage(kUsage);
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  oncall_scheduler::schedule(FLAGS_num_weeks, 1);
  return EXIT_SUCCESS;
}

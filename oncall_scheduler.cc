#include "absl/strings/str_cat.h"

#include "ortools/base/commandlineflags.h"
#include "ortools/base/integral_types.h"
#include "ortools/base/logging.h"
#include "ortools/sat/cp_model.h"

#include <vector>

using operations_research::Domain;

using operations_research::sat::BoolVar;
using operations_research::sat::CpModelBuilder;
using operations_research::sat::LinearExpr;
using operations_research::sat::Model;
using operations_research::sat::SolveCpModel;
using operations_research::sat::CpSolverResponse;
using operations_research::sat::CpSolverResponseStats;

namespace oncall_scheduler {


struct Person {
    std::string name;
    std::string location_name;
};

struct Rotation {
    std::vector<Person> persons;
};

static bool was_primary_oncall(int week, Person p) {
    return p.name == "me";
}

static bool was_secondary_oncall(int week, Person p) {
    return p.name == "be";
}

// Schedules #`shifts` considering `lookback` number of previous shifts.
void schedule(const int num_shifts, const int lookback) {
    const auto rotation = Rotation{
            .persons = std::vector<Person>{
                    Person{"me", "abc"},
                    Person{"be", "abc"},
                    Person{"ce", "def"},
                    Person{"fe", "def"},
            },
    };

    CpModelBuilder builder;


    std::vector<std::vector<BoolVar>> primary_shifts(lookback + num_shifts);
    std::vector<std::vector<BoolVar>> secondary_shifts(lookback + num_shifts);

    // Look back to previous and already scheduled shifts and add the truths.
    for (int i = 0; i < lookback; ++i) {
            for (int p_no = 0; p_no < rotation.persons.size(); ++p_no) {
                const Person& p = rotation.persons[p_no];
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
                primary_shifts[i].push_back(p_shift);
                secondary_shifts[i].push_back(s_shift);
            }
    }

    // Create the shifts we need to schedule.
    for (int i = 0; i < num_shifts; ++i) {
            int shift = i + lookback;
            for (int p_no = 0; p_no < rotation.persons.size(); ++p_no) {
                const Person& p = rotation.persons[p_no];
                auto p_shift = builder.NewBoolVar()
                                    .WithName(absl::StrCat("p_shift_", shift, "_", p.name));
                auto s_shift = builder.NewBoolVar()
                                    .WithName(absl::StrCat("s_shift_", shift, "_", p.name));
                primary_shifts[shift].push_back(p_shift);
                secondary_shifts[shift].push_back(s_shift);

                // Person must not be primary and secondary at the same time.
                builder.AddLessOrEqual(LinearExpr::BooleanSum({p_shift, s_shift}), 1);

                // We will not be primary or secondary back to back.
                if (shift >= 1) {
                        const BoolVar& previous_p_shift = primary_shifts[shift - 1][p_no];
                        const BoolVar& previous_s_shift = secondary_shifts[shift - 1][p_no];
                        const auto p_sum = LinearExpr::BooleanSum({p_shift, previous_p_shift});
                        builder.AddLessOrEqual(p_sum, 1);
                        const auto s_sum = LinearExpr::BooleanSum({s_shift, previous_s_shift});
                        builder.AddLessOrEqual(s_sum, 1);
                }
            }

            // Each shift must have a person assigned.
            builder.AddEquality(LinearExpr::BooleanSum(primary_shifts[shift]), 1);
            builder.AddEquality(LinearExpr::BooleanSum(secondary_shifts[shift]), 1);
    }

    // TODO(zecke): Make sure everyone has an equal number of assignments
    const int total_shifts = num_shifts + lookback;
    const int min_shifts = (total_shifts) / rotation.persons.size();
    const int max_shifts = ((total_shifts) % rotation.persons.size()) == 0 ? (min_shifts) : min_shifts + 1;
    LOG(INFO) << "min: " << min_shifts << " max: " << max_shifts;

    for (int p_no = 0; p_no < rotation.persons.size(); ++p_no) {
            std::vector<BoolVar> p_person_shifts, s_person_shifts;

            for (const std::vector<BoolVar>& shifts : primary_shifts) {
                    p_person_shifts.push_back(shifts[p_no]);
            }
            for (const std::vector<BoolVar>& shifts : secondary_shifts) {
                    s_person_shifts.push_back(shifts[p_no]);
            }

            // Assign equal number of primary shifts.
            builder.AddLessOrEqual(min_shifts, LinearExpr::BooleanSum(p_person_shifts));
            builder.AddLessOrEqual(LinearExpr::BooleanSum(p_person_shifts), max_shifts);

            // Assign equal number of secondary shifts.
            builder.AddLessOrEqual(min_shifts, LinearExpr::BooleanSum(s_person_shifts));
            builder.AddLessOrEqual(LinearExpr::BooleanSum(s_person_shifts), max_shifts);
    }


    // TODO(zecke): Honor OOO, public holidays or other shifts. We might need to do
    // this in two places.
    // 1.) E.g. OOO or other shift should be a hard FalseVar
    // 2.) public holiday should be a penalty...

    // TODO(zecke): Optimize for space between two primary shifts..


    Model model;
    const CpSolverResponse response = SolveCpModel(builder.Build(), &model);
    LOG(INFO) << CpSolverResponseStats(response);


    for (int i = 0; i < num_shifts; ++i) {
        int shift = i + lookback;

        for (int p = 0; p < rotation.persons.size(); ++p) {
            const Person person = rotation.persons[p];

            if (SolutionIntegerValue(response, primary_shifts[shift][p])) {
                    LOG(INFO) << "Primary Shift #" << shift << " for: " << person.name;
            }
        }
    }

    for (int i = 0; i < num_shifts; ++i) {
        int shift = i + lookback;

        for (int p = 0; p < rotation.persons.size(); ++p) {
            const Person person = rotation.persons[p];

            if (SolutionIntegerValue(response, secondary_shifts[shift][p])) {
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

  oncall_scheduler::schedule(4, 1);
  return EXIT_SUCCESS;
}

# Oncall scheduling proof of concept

This should be a set of tools that help to schedule an oncall but is at a
humble beginning. The first goal is to support:

* Schedule primary and secondar for oncall.
* Primary and secondary are different.
* Honor OOO.
* Honor public holidays (multi-location team).
* Primary not back to back.
* Rolling window of assignments (for incremental assignments)


## Considerations

We do this with the following constraints and objective:

1.) The number of shifts assigned across all members of a rotation should
be equal over a long enough time range. At the same time a rotation might
see members join and leave. We solve this by looking back and filling the
already scheduled shifts with FalseVar/TrueVar

2.) We MUST NOT have two shifts in a row. We solve this by
looking back at the previous shift (if it can exist). This means we should
always look one week back:

```c++
    const BoolVar& previous_p_shift = primary_shifts[shift - 1][p_no];
    const auto p_sum = LinearExpr::BooleanSum({p_shift, previous_p_shift});
    builder.AddLessOrEqual(p_sum, 1);

    const BoolVar& previous_s_shift = secondary_shifts[shift - 1][p_no];
    const auto s_sum = LinearExpr::BooleanSum({s_shift, previous_s_shift});
    builder.AddLessOrEqual(s_sum, 1);
```

3.) The scheduling works on weeks from 0...lookback...number of shifts. Which
is a sliding window. We will have glue around to map this properly.

4.) A person MUST NOT be primary and secondary at the same time.

```c++
    builder.AddLessOrEqual(LinearExpr::BooleanSum({p_shift, s_shift}), 1);
```

5.) Each shift must be assigned

```c++
    builder.AddEquality(LinearExpr::BooleanSum(primary_shifts[shift]), 1);
    builder.AddEquality(LinearExpr::BooleanSum(secondary_shifts[shift]), 1);
```


6.) We try to have the constraint that everyonr has the same amount of shifts. But
with OOO and other bits that might not be possible. This is why we make it soft by
adding surplus and deficit vars and then try to minimize them.

```
shifts_worked_by_person > min_shifts + surplus[p] - deficit[p]
shifts_worked_by_person < max_shifts + surplus[p] - deficit[p]


7.) We can handle OOO by adding == False constraints for a specific shift

8.) We can handle public holidays by assigning a high cost and use the same mimimize
objective.

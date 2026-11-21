"""ftwin: run the model-checking side and the Lean side of a twin lab and compare.

    ftwin run counter            # all SBY tasks + Lean theorems, side-by-side table
    ftwin run counter --json out/counter.json

Each design directory `rtl/<design>/` has a `twin.toml` naming its SBY tasks and,
for each assertion label, the Lean theorem that proves it.
"""

# Feedback welcome!

Currently, the best way to help out is to contribute to the discussion on how changing certain definitions or adding specific metaprogramming can help improve usability (see also the `Examples.lean` file). Some good alternatives have also been suggested in this thread: [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Many-sorted.20model.20theory).

## Contributing code

Feel free to create pull requests for small changes and improvements to e.g. a single theorem. For larger proposed changes, please first raise an issue on the GitHub page so that it can be discussed.

Once the fundamental definitions are more stable, a blueprint plan will be added to reach at least the following results:

- An API to compare and transfer results about the one-sorted `Language` to `MSLanguage Unit`.
- The definition of a map between languages on different sorts, and a proof of the many-sorted compactness theorem from the one-sorted one by using the map `MSLanguage Sorts -> MSLanguage Unit`
- Types in many-sorted logic and quantifier elimination tests.

These results will pave the way for formalizing the model theory of valued fields, and possibly many more areas of logic.
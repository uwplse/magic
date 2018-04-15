This plugin is to help you learn how to write fun spells (supertactics) using the Coq plugin
infrastructure and understand the magic behind them.
There are a number of example spells and some exercises to try out yourself.

# Citing

If you build on any of the commands or tactics here and then publish a paper, please cite the 
[PUMPKIN PATCH](http://tlringer.github.io/pdf/pumpkinpaper.pdf) paper, since the interesting commands and tactics
all build on the factoring component from that paper.

# Building

The plugin runs on Coq 8.6. Just run `make`.

# Example Spells

There are a number of toy example spells in [magic.ml4](/src/magic.ml4) for the sake of demonstration.
The test code for these examples is in [Examples.v](/coq/Examples.v). Since these are purely demonstrative,
they are not guaranteed to work for code outside of these examples.

Many of the examples are simple versions of functionality from [PUMPKIN PATCH](http://github.com/uwplse/PUMPKIN-PATCH).
If you are curious, the paper is [here](http://tlringer.github.io/pdf/pumpkinpaper.pdf).

# Exercises

Exercises are in [magic.ml4](/src/magic.ml4). Tests for these exercises are in the [exercises](/coq/exercises/) directory.
The comments for each exercise note which file contains the test for that exercise.

# Pop Culture References

Any pop culture references in this repository are references to Harry Potter. This is just for fun,
since this was originally presented in a themed lecture to a group of graduate students.
If you do not understand the pop culture references, don't worry about them.

# Other Questions

If you have any questions, please contact Talia Ringer (tringer@cs.washington.edu) or cut an issue in this 
GitHub repository.

## Capstone Emulator

This is a very straightforward (and brute-force) implementation of
Capstone. While nothing good could be said of its performance, it does
have the benefit of being simple to tweak and handy to use.

Given a machine state and a set of instructions, it executes them one by one, updating the machine state.

### Setting up

Simply install a Haskell toolchain. You can use GHC packages
maintained by your distribution.

### Usage

You can compile the source code to a binary with

    ghc Emulator.hs

You can also run it directly with `runghc Emulator.hs`.

The code as well as other configurations should be supplied in the
standard input. You may check the files in the `tests` folder for
examples, and pipe them through the standard input (they are
out-of-date and do not work any more):

    `runghc Emulator.hs < file-to-run`

The input can also be generated from the Capstone compiler:

    `capstone-c source-code.c | runghc Emulator.hs`

### Input Format

The emulator takes inputs as:

    -Machine State : memsize, gprcnt, clock, capcnt, segcnt
    -baseaddr, segsize
    -List of instructions

The emulator executes the instructions one by one, following Capstone semantics, to reach an end machine state.

### Possible Outputs

If the emulator has run every instruction successfully, it eventually reaches a halted state, otherwise it throws an error accordingly.

For example, when trying to `scco` a sealed capability, the compiler will show

    Error scco

## TEECap Emulator

This is a very straightforward (and brute-force) implementation of
TEECap. While nothing good could be said of its performance, it does
have the benefit of being simple to tweak and handy to use.

### Setting up

Simply install a Haskell toolchain. You can use GHC packages
maintained by your distribution.

### Usage

You can compile the source code to a binary with

    ghc Emulator.hs

You can also run it directly with `runghc Emulator.hs`.

The code as well as other configurations should be supplied in the
standard input. You may check the files in the `tests` folder for
examples, and pipe them through the standard input:

    `runghc Emulator.hs < file-to-run`

The input can also be generated from the TEECap compiler:

    `teecap-c source-code.c | runghc Emulator.hs`


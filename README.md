# Iris demo of a concurrent bank

[![CI](https://github.com/tchajed/iris-bank-demo/workflows/CI/badge.svg)](https://github.com/tchajed/iris-bank-demo/actions)

Demo of using Iris to prove an that the balances of a concurrent bank sum to
zero.

The setup here is to create a "bank", which consists of two balances (which are
mathematical integers). The bank has two operations: a `transfer` operation to
move from one account to the other and a `check_consistency` operation that
locks both balances and checks if the balances add up to zero. What we prove is
that `check_consistency` always returns true, even with concurrent `transfer`s.

The demo is entirely in a single well-commented Coq file [demo.v](src/demo.v).

## Compiling

To compile, just run `make`. You'll need Coq with Iris installed. It should work
on Coq v8.11, but there's no CI (yet) and it's only tested on Coq master so who
knows.

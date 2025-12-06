# Non-interference formalization

## Files 

- Identifier: represent variables as integers
- Environment: represent states as partial map 
- Imperative: define expressions, commands, configurations, expression evaluation, configuration step
- Types: define low and high
- WellFormedness: the well-formedness of memory state and level context
- Augmented: steps with events
- Bridge: the bridge relation
- Adequacy: adequacy lemma for event steps and bridge relation
- NIexp: non-interference lemma for expression
- NIBridge: non-interference lemma for bridge
- NI: the non-interference lemma

## Commands

To setup the ROCQ environment

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.18.0
opam install coq-dpdgraph -y
coqtop -R . dpdgraph -I .
```

To check that the environment is correct:

```shell
liulang@Mac-mini test_lang % coqc -v
The Coq Proof Assistant, version 8.18.0
```

To run the proof:

```shell 
make clean 
make
```

and you should see the output:

```text
coqc -Q . TL lib/InductionPrinciple.v
coqc -Q . TL Identifier.v
coqc -Q . TL Environment.v
coqc -Q . TL Imperative.v
coqc -Q . TL Types.v
coqc -Q . TL Augmented.v
coqc -Q . TL WellFormedness.v
coqc -Q . TL LowEq.v
coqc -Q . TL Bridge.v
coqc -Q . TL Adequacy.v
coqc -Q . TL NIexp.v
coqc -Q . TL NIBridge.v
coqc -Q . TL NI.v
```

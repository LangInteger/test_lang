Files 

- Identifier: represent variables as integers
- Environment: represent states as partial map 
- Imperative: define expressions, commands, configurations, expression evaluation, configuration step
- Types: define low and high
- Augmented: steps with events

Command

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.18.0
opam install coq-dpdgraph -y
coqtop -R . dpdgraph -I .
```
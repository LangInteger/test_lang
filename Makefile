COQFILES = \
  ./lib/InductionPrinciple.v \
	Identifier.v \
	Environment.v \
	Imperative.v \
	Types.v \
	Augmented.v \
	WellFormedness.v \
	LowEq.v \
	Bridge.v \
	Adequacy.v \
	NIexp.v \
	NIBridge.v \
	NI.v

COQC = coqc -Q . TL

all: $(COQFILES:.v=.vo)

%.vo: %.v
	$(COQC) $<

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux .*.aux
	rm -f lib/*.vo lib/*.glob lib/*.vok lib/*.vos lib/*.aux lib/.*.aux
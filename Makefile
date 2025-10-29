COQFILES = \
	Identifier.v \
	Environment.v \
	Imperative.v \
	Types.v \
	Augmented.v \
	WellFormedness.v \
	LowEq.v

COQC = coqc -Q . TL

all: $(COQFILES:.v=.vo)

%.vo: %.v
	$(COQC) $<

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux .*.aux
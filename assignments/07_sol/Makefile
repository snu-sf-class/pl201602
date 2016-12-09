DFILES = D.v SfLib.v Basics.v Maps.v Imp.v Smallstep.v Types.v
PFILES = $(shell find P??.v)
EFILES = $(shell find E??_??.v)

POFILES = $(patsubst %.v,%.vo,$(PFILES))
EOFILES = $(patsubst %.v,%.vo,$(EFILES))

all: $(DFILES) $(PFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(POFILES)

check:
	bash ./check.sh

eval: $(DFILES) $(PFILES) $(EFILES) Makefile.coq check
	$(MAKE) -f Makefile.coq $(EOFILES)

submission:
	zip submission.zip P??.v

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm _CoqProject Makefile.coq

Makefile.coq: Makefile $(PFILES) $(EFILES)
	(echo -R . Assignment $(DFILES) $(PFILES) $(EFILES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

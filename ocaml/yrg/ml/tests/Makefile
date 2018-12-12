.PHONY: check prepare clean

POSITIVE=$(wildcard *.ml)
NEGATIVE=$(wildcard *.ko)
RESULTS=$(POSITIVE:.ml=.ml.out) $(NEGATIVE:.ko=.ko.out)

MINIML=../miniml.byte $(OPTS)

prepare:
	@ rm -f failures *.out

check: prepare $(RESULTS)
	@ if [ -e failures ]; then echo Failures:; cat failures; else echo 'Perfect!'; fi

%.ml.out: %.ml
	@ ($(MINIML) $< > $@ && echo "[OK]" $<) || (echo "[KO]" $< && echo $< >> failures)
	@ cat $@

%.ko.out: %.ko
	@ ($(MINIML) $< > $@ && (echo "[KO]" $< && echo $< >> failures)) || echo "[XFAIL]" $<;
	@ cat $@


clean:
	rm -f *.out failures *~


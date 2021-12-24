include Makefile

fw:
	ls *.fw | grep -v [0-9][.]fw

.PHONY: parse

parse:  $(patsubst %.fw, %.fws, $(FILES))

%.fws: %.fw  $(FOMEGA)
	$(FOMEGA) --reparse --reprint --no-typing $< > $@ || \
	(rm -f $@ && $(FOMEGA) $< --reprint --no-typing > $*.s.fw && false)

clean::
	rm -f *.fws *.s.fw


.PHONY: html clean

html: README.html

clean:
	rm -f README.html *~

README.html: README.md
	pandoc -s -f markdown -t html -o $@ $<

PATH := /usr/local/smlnj-110.65/bin/:$(PATH)
SML = sml
VERSION = 0.2.1

TESTFILES = core fib link seal

all:
	$(SML) <wrap-smlnj.sml

check:
	./mixml $(TESTFILES:%=%.mixml)

checkx:
	./mixml -x $(TESTFILES:%=%.mixml)

tar:
	mkdir mixml-$(VERSION) && \
	cp *.sml *.grm *.lex *.cm *.mixml Makefile mixml *.txt ../syntax.pdf mixml-$(VERSION) && \
	tar czf mixml-$(VERSION).tgz mixml-$(VERSION) && \
	rm -r mixml-$(VERSION)

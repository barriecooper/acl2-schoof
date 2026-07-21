.PHONY: setup certify certify-one test check-trust clean
BOOK ?=
setup:
	./scripts/install-acl2.sh
certify: setup check-trust
	./scripts/certify.sh
certify-one: setup check-trust
	@test -n "$(BOOK)" || { echo 'usage: make certify-one BOOK=books/path/book.lisp' >&2; exit 2; }
	./scripts/certify-one.sh "$(BOOK)"
test: setup check-trust
	./scripts/test.sh
check-trust:
	./scripts/check-trust.sh
clean:
	find books tests -type f \( -name '*.cert' -o -name '*.cert.out' -o -name '*.pcert0' -o -name '*.port' -o -name '*.o' -o -name '*.fasl' -o -name '*.lx64fsl' -o -name '*.log' -o -name 'cert.acl2' \) -delete
	rm -f Makefile-tmp

# Makefile for the canprove Emacs package.
#
# Single source of truth for the version: VER below.
#   make sync-version   propagate VER into canprove.el and canprove-pkg.el
#   make check-version  fail if the three places disagree (for CI)
#   make tar            sync, verify, and build the tarball
#   make bump V=1.2.3   update VER here and propagate it

PKG   := canprove
VER   := 0.1.0

MAIN  := $(PKG).el
CALC  := $(PKG)-calc.el
PKGEL := $(PKG)-pkg.el
FILES := $(MAIN) $(CALC) $(PKGEL)

DIR   := $(PKG)-$(VER)
TAR   := $(DIR).tar

TESTS := $(PKG)-tests.el

.PHONY: all tar sync-version check-version bump test clean install

all: tar

## --- version ----------------------------------------------------------

sync-version:
	@sed -i.bak 's|^;; Version: .*|;; Version: $(VER)|' $(MAIN) && rm -f $(MAIN).bak
	@sed -i.bak 's|^(define-package "$(PKG)" "[^"]*"|(define-package "$(PKG)" "$(VER)"|' \
	    $(PKGEL) && rm -f $(PKGEL).bak
	@echo "Version -> $(VER) in $(MAIN) and $(PKGEL)"

check-version:
	@el=$$(sed -n 's/^;; Version: *//p' $(MAIN) | head -1); \
	pk=$$(sed -n 's/^(define-package "[^"]*" "\([^"]*\)".*/\1/p' $(PKGEL) | head -1); \
	if [ "$$el" != "$(VER)" ] || [ "$$pk" != "$(VER)" ]; then \
	  printf 'version mismatch:\n  Makefile       = %s\n  %-14s = %s\n  %-14s = %s\n' \
	    "$(VER)" "$(MAIN)" "$$el" "$(PKGEL)" "$$pk"; \
	  exit 1; \
	fi; \
	echo "versions agree: $(VER)"

bump:
	@test -n "$(V)" || { echo "usage: make bump V=1.2.3"; exit 1; }
	@sed -i.bak 's|^VER   := .*|VER   := $(V)|' Makefile && rm -f Makefile.bak
	@$(MAKE) sync-version VER=$(V)

## --- build ------------------------------------------------------------

tar: sync-version check-version
	@rm -rf $(DIR) $(TAR)
	@mkdir -p $(DIR)
	@cp $(FILES) $(DIR)/
	@tar cf $(TAR) $(DIR)
	@echo "built $(TAR)"

install: tar
	emacs --batch --eval \
	  "(progn (require 'package) (package-initialize) \
	     (package-install-file \"$(CURDIR)/$(TAR)\"))"

test:
	emacs -Q --batch -L . -l $(TESTS) -f ert-run-tests-batch-and-exit

compile:
	emacs -Q --batch -L . -f batch-byte-compile $(MAIN) $(CALC)

clean:
	@rm -rf $(DIR) $(TAR) *.elc

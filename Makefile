GHC=ghc
GHCFLAGS= -O2

default:
	ghc --make Main.hs

install-deps: # poor man's cabal
	cabal update
	cabal install newtype

clean:
	rm -rf *.o *.hi

install-hasktags:
	cabal update
	cabal install hasktags

TAGS:
	hasktags --ignore-close-implementation --etags .

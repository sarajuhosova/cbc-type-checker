run: compile
	@cabal run

build: compile
	@echo "Building the Haskell project..."
	@cabal build
	@echo ""

compile:
	@echo "Generating Haskell library with Agda2HS..."
	@chmod +x compile.sh
	@./compile.sh
	@echo ""

install :
	@cabal new-install --overwrite-policy=always

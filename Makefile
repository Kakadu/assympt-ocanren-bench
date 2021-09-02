.PHONY: all watch test

all:
	dune build src/main.exe --display=quiet && dune exec src/main.exe --display=quiet

watch:
	dune build -w

test:
	dune test

clean:
	@dune clean

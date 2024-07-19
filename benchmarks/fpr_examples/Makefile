


CXX_SOURCES = \
	test1.c \
	test2.c \
	test3.c \
	test4.c \
	test5.c \
	test6.c \
	test7.c \
	test8.c \
	test9.c \

BINARIES = $(patsubst %.c,%.out,$(CXX_SOURCES))
ASSEMBLY = $(patsubst %.c,asm/%.s,$(CXX_SOURCES))
VIRFILES = $(patsubst %.c,virfiles/%.vir,$(CXX_SOURCES))


all: virfiles assembly binaries

binaries: $(BINARIES)

assembly: $(ASSEMBLY)

virfiles: $(VIRFILES)

%.out: %.c
	riscv64-unknown-elf-gcc -fstack-usage -g -gdwarf -fno-jump-tables -march=rv64imafd -mabi=lp64d -o $@ $^

asm/%.s: %.c
	riscv64-unknown-elf-gcc -S -o $@ $^

virfiles/%.vir: %.out
	riscverifier --vectre_programs $@ -f main $^

clean:
	rm -f $(BINARIES)
	rm -f $(ASSEMBLY)
	rm -f $(VIRFILES)

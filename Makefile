CXXFLAGS=-std=c++11 -Wall -O3 -march=native -fwhole-program
LDFLAGS=-flto -lgmp -lgmpxx -lpthread
TURBOPFOR=../TurboPFor
TURBOPFOR_OBJS=bitpack.o bitpackv.o vp4dc.o vp4dd.o bitunpack.o bitunpackv.o bitutil.o
TURBOPFOR_OBJLIBS=$(addprefix $(TURBOPFOR)/,$(TURBOPFOR_OBJS))

A273525-rocket: A273525.cpp TurboPFor
	g++ $< $(TURBOPFOR_OBJLIBS) -o $@ -DROCKET -I$(TURBOPFOR) $(CXXFLAGS) $(LDFLAGS)

A273525: A273525.cpp TurboPFor
	g++ $< $(TURBOPFOR_OBJLIBS) -o $@ -I$(TURBOPFOR) $(CXXFLAGS) $(LDFLAGS)

clean:
	rm -f A273525 A273525-rocket

test: A273525
	./A273525 -t intset
	./A273525 -t dryrun_s4
	./A273525 -k 125 | grep -qF " = 33947876" && echo 'Passed: -k 125'

TurboPFor:
	cd $(TURBOPFOR) && $(MAKE) $(TURBOPFOR_OBJS)

.PHONY: clean test TurboPFor

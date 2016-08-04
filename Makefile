CXXFLAGS=-std=c++11 -Wall -O3 -march=native -fwhole-program
LDFLAGS=-flto -lgmp -lgmpxx -lpthread

A273525-rocket: A273525.cpp
	g++ $< -o $@ -DROCKET $(CXXFLAGS) $(LDFLAGS)

A273525: A273525.cpp
	g++ $< -o $@ $(CXXFLAGS) $(LDFLAGS)

clean:
	rm -f A273525 A273525-rocket

test: A273525
	./A273525 -t intset
	./A273525 -t dryrun_s4

.PHONY: clean test

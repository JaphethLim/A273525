CXXFLAGS=-std=c++11 -Wall -O3 -march=native -fwhole-program
LDFLAGS=-flto -lgmp -lgmpxx -lpthread

A273525: A273525.cpp
	g++ A273525.cpp -o A273525 $(CXXFLAGS) $(LDFLAGS)

clean:
	rm A273525

test: A273525
	./A273525 -t intset
	./A273525 -t dryrun_s4

.PHONY: clean test

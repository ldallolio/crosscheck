// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
//
// OTAWA with Cortex-M0 instruction timings: the IPET bound of a function in cycles.
//
//   m0time ELF FUNCTION FLOWFACTS TIMES
//
// TIMES has one line per instruction, "label offset cycles": the cycles of the
// instruction at that offset from the function's label, from the timing table of
// benchmarks/cycles/m0.py (Table 3-1 of Arm DDI 0432C, compared row by row by
// test_m0.py). A conditional branch is charged as taken (3 cycles), whichever edge
// leaves the block: the block times are upper bounds, and OTAWA's edge times are not
// used. Everything else is OTAWA's: the decoding and control-flow graphs of the ELF
// (its ARM loader), the flow facts (FFX), the ILP and its solution.
//
// The Cortex-M0 has no cache and executes in order with fixed per-instruction times
// (zero wait-state memory), so the time of a block is the sum of the times of its
// instructions: no pipeline description is needed. An instruction without a time in
// TIMES stops the program (exit status 2).

#include <otawa/otawa.h>
#include <otawa/cfg/features.h>
#include <otawa/flowfact/features.h>
#include <otawa/ipet.h>
#include <otawa/proc/BBProcessor.h>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <utility>

using namespace otawa;

namespace {

std::map<std::pair<std::string, unsigned long>, long> times;

class M0Time: public BBProcessor {
public:
	static p::declare reg;
	M0Time(): BBProcessor(reg) { }

protected:
	void processBB(WorkSpace *, CFG *cfg, Block *b) override {
		if(!b->isBasic()) {
			ipet::TIME(b) = 0;	// entry, exit and call blocks: no instruction
			return;
		}
		BasicBlock *bb = b->toBasic();
		elm::String l = cfg->label();
		std::string label(l.chars(), l.length());
		unsigned long base = cfg->address().offset();
		ot::time t = 0;
		for(auto i: *bb) {
			unsigned long off = i->address().offset() - base;
			auto it = times.find({label, off});
			if(it == times.end()) {
				std::cerr << "no time for " << label << "+0x" << std::hex << off << std::dec << "\n";
				std::exit(2);
			}
			t += it->second;
		}
		ipet::TIME(bb) = t;
	}
};

p::declare M0Time::reg = p::init("M0Time", Version(1, 0, 0))
	.maker<M0Time>()
	.extend<BBProcessor>()
	.require(COLLECTED_CFG_FEATURE)
	.provide(ipet::BB_TIME_FEATURE);

}	// namespace

int main(int argc, char **argv) {
	if(argc != 5) {
		std::cerr << "usage: m0time ELF FUNCTION FLOWFACTS TIMES\n";
		return 1;
	}
	{
		std::ifstream in(argv[4]);
		std::string line;
		while(std::getline(in, line)) {
			std::istringstream ls(line);
			std::string label;
			unsigned long off;
			long c;
			if(ls >> label >> off >> c) times[{label, off}] = c;
		}
	}
	try {
		PropList props;
		TASK_ENTRY(props) = argv[2];
		FLOW_FACTS_PATH(props) = elm::sys::Path(argv[3]);
		WorkSpace *ws = MANAGER.load(argv[1], props);
		ws->require(COLLECTED_CFG_FEATURE, props);
		ws->run<M0Time>(props);
		ws->require(ipet::WCET_FEATURE, props);
		std::cout << "WCET[" << argv[2] << "] = " << ipet::WCET(ws) << " cycles\n";
		delete ws;
	}
	catch(otawa::Exception& e) {
		std::cerr << "ERROR: " << e.message() << "\n";
		return 3;
	}
	return 0;
}

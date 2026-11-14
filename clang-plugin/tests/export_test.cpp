// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Flow-fact (FFX, AIS, AIS2) and SARIF outputs (src/analysis/Export.hpp). The
// formats themselves are checked against real readers by tests/check_exports.py.
#include <gtest/gtest.h>

#include "analysis/Export.hpp"
#include "test_support.hpp"

using namespace crosscheck;
using crosscheck::testing::check;

namespace {

bool has(const std::string& text, const std::string& part) { return text.find(part) != std::string::npos; }

const char* kCode = R"(
  CROSSCHECK_REALTIME int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
    int s = 0;
    for (int i = 0; i < n; ++i) s += a[i];
    return s;
  }
  int caller(const int* a) { return sum(a, 10); }
  CROSSCHECK_REALTIME int poll(volatile int* r) {
    int k = 0;
    while (*r == 0) { CROSSCHECK_LOOP_BOUND(7); k++; }
    return k;
  }
)";

Options withFacts(const std::string& format, const std::string& context = "every-call") {
  Options o;
  o.analyzeAll = true;
  o.flowFactsPath = "unused";
  o.flowFactsFormat = format;
  o.flowFactsContext = context;
  return o;
}

TEST(Export, FfxLoopBoundsForEveryCall) {
  Options o = withFacts("ffx");
  std::string x = toFlowFacts(check(kCode, o), o);
  EXPECT_TRUE(has(x, "<flowfacts>")) << x;
  EXPECT_TRUE(has(x, "line=\"5\" maxcount=\"64\"")) << x;
  EXPECT_TRUE(has(x, "crosscheck-function=\"sum\"")) << x;
  // The annotated loop is an assumption: not exported, but counted.
  EXPECT_FALSE(has(x, "maxcount=\"7\"")) << x;
  EXPECT_TRUE(has(x, "1 loop bound(s) stated by annotations are assumptions")) << x;
  EXPECT_FALSE(has(x, "<!-- --")) << x;
}

TEST(Export, FfxInTheProgramsContexts) {
  Options o = withFacts("ffx", "program");
  o.entry = "caller";
  std::string x = toFlowFacts(check(kCode, o), o);
  EXPECT_TRUE(has(x, "line=\"5\" maxcount=\"10\"")) << x;  // sum(a, 10)
  EXPECT_TRUE(has(x, "in the calling contexts of the analysed program (entry: caller)")) << x;
}

TEST(Export, AisNamesRoutinesByTheirLinkerName) {
  Options o = withFacts("ais");
  std::string a = toFlowFacts(check(kCode, o), o);
  EXPECT_TRUE(has(a, "loop \"_Z3sumPKii\" + 1 loops max 64;")) << a;
  EXPECT_TRUE(has(a, "not validated with aiT")) << a;
  o.flowFactsFormat = "ais2";
  std::string b = toFlowFacts(check(kCode, o), o);
  EXPECT_TRUE(has(b, "loop \"_Z3sumPKii.L1\" { bound: 0 .. 64; }")) << b;
}

TEST(Export, FormatFromTheExtension) {
  Options o;
  o.flowFactsPath = "x.ais";
  EXPECT_EQ(flowFactsFormat(o), "ais2");
  o.flowFactsPath = "x.ffx";
  EXPECT_EQ(flowFactsFormat(o), "ffx");
  EXPECT_FALSE(o.parse("flowfacts-format=sweet"));
  EXPECT_FALSE(o.parse("flowfacts-context=sometimes"));
}

TEST(Export, SarifErrorsAndNotes) {
  Options o;
  o.analyzeAll = true;
  Report r = check(R"(
    CROSSCHECK_REALTIME int spin(volatile int* r) { int k = 0; while (*r) k++; return k; }
    CROSSCHECK_DEADLINE(5) int slow(CROSSCHECK_RANGE(0, 9) int n) {
      int s = 0;
      for (int i = 0; i < n; i++) s++;
      return s;
    })", o);
  std::string s = toSarif(r, o);
  EXPECT_TRUE(has(s, "\"version\": \"2.1.0\"")) << s;
  EXPECT_TRUE(has(s, "\"ruleId\": \"rejected\", \"ruleIndex\": 0, \"level\": \"error\"")) << s;
  EXPECT_TRUE(has(s, "\"ruleId\": \"deadline\", \"ruleIndex\": 1, \"level\": \"error\"")) << s;
  EXPECT_TRUE(has(s, "\"ruleId\": \"bound\"")) << s;
  EXPECT_TRUE(has(s, "\"startLine\": 3, \"startColumn\": 64")) << s;  // the loop of `spin` (line 1 is the test preamble)
}

}  // namespace

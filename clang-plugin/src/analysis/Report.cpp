// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#include "Report.hpp"

#include <cstdio>

namespace crosscheck {

std::string jsonQuote(const std::string& s) {
  std::string out = "\"";
  for (unsigned char c : s) {
    switch (c) {
      case '"': out += "\\\""; break;
      case '\\': out += "\\\\"; break;
      case '\n': out += "\\n"; break;
      case '\t': out += "\\t"; break;
      default:
        if (c < 0x20) {
          char buf[8];
          std::snprintf(buf, sizeof buf, "\\u%04x", c);
          out += buf;
        } else {
          out += static_cast<char>(c);
        }
    }
  }
  return out + "\"";
}

namespace {

std::string quote(const std::string& s) { return jsonQuote(s); }

std::string strings(const std::vector<std::string>& v) {
  std::string out = "[";
  for (std::size_t i = 0; i < v.size(); ++i) out += (i ? ", " : "") + quote(v[i]);
  return out + "]";
}

}  // namespace

std::string Report::toJson() const {
  std::string out = "{\n  \"functions\": [";
  for (std::size_t i = 0; i < functions.size(); ++i) {
    const FunctionReport& f = functions[i];
    out += i ? ",\n    {" : "\n    {";
    out += "\n      \"name\": " + quote(f.name);
    out += ",\n      \"symbol\": " + quote(f.symbol);
    out += ",\n      \"file\": " + quote(f.file);
    out += ",\n      \"line\": " + std::to_string(f.line);
    out += ",\n      \"ok\": " + std::string(f.ok ? "true" : "false");
    out += ",\n      \"wcet\": " + (f.bounded ? std::to_string(f.wcet) : std::string("null"));
    out += ",\n      \"contexts\": " + std::to_string(f.contexts);
    out += ",\n      \"wcet_in_context\": " +
           (f.wcetInContext ? std::to_string(*f.wcetInContext) : std::string("null"));
    out += ",\n      \"deadline\": " + (f.deadline ? std::to_string(*f.deadline) : std::string("null"));
    if (f.interruptHandler) out += ",\n      \"interrupt_handler\": true";
    if (f.responseTime) out += ",\n      \"response_time\": " + std::to_string(*f.responseTime);
    out += ",\n      \"loops\": [";
    for (std::size_t j = 0; j < f.loops.size(); ++j) {
      const LoopReport& l = f.loops[j];
      out += std::string(j ? ", " : "") + "{\"file\": " + quote(l.file) +
             ", \"line\": " + std::to_string(l.line) + ", \"column\": " + std::to_string(l.column) +
             ", \"bound\": " + std::to_string(l.bound) +
             ", \"verified\": " + (l.verified ? "true" : "false") +
             ", \"in_context\": " + (l.inContext ? std::to_string(*l.inContext) : std::string("null")) +
             ", \"potential\": " + quote(l.potential) + "}";
    }
    out += "]";
    out += ",\n      \"recursion\": ";
    if (f.recursion) {
      out += "{\"activations\": " + std::to_string(f.recursion->activations) +
             ", \"branching\": " + std::to_string(f.recursion->branching) +
             ", \"depth\": " + (f.recursion->depth ? std::to_string(*f.recursion->depth) : std::string("null")) +
             ", \"potential\": " + quote(f.recursion->potential) + "}";
    } else {
      out += "null";
    }
    out += ",\n      \"certificate\": " + quote(f.certificate);
    out += ",\n      \"certificate_bound\": " +
           (f.certificateBound ? std::to_string(*f.certificateBound) : std::string("null"));
    out += ",\n      \"certificate_summary\": " + quote(f.certificateSummary);
    out += ",\n      \"assumptions\": " + strings(f.assumptions);
    out += ",\n      \"errors\": " + strings(f.errors);
    out += "\n    }";
  }
  out += functions.empty() ? "]\n}\n" : "\n  ]\n}\n";
  return out;
}

}  // namespace crosscheck

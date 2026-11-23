#ifndef PROFILER__HPP__
#define PROFILER__HPP__

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <string>
#include <vector>
#include <algorithm>

// Lightweight call/time profiler. Timers accumulate (calls, seconds) under a name,
// counters accumulate plain numbers. Collection is always on (it is cheap as long as
// timers are not put on very hot functions); the report is printed only if enabled().

namespace ufo
{
  namespace prof
  {
    typedef std::chrono::steady_clock Clock;

    struct Stat
    {
      size_t calls = 0;
      double secs = 0;
    };

    inline bool& enabled() { static bool e = false; return e; }
    inline Clock::time_point& startTime() { static Clock::time_point t = Clock::now(); return t; }
    inline std::map<std::string, Stat>& timers() { static std::map<std::string, Stat> s; return s; }
    inline std::map<std::string, size_t>& counters() { static std::map<std::string, size_t> c; return c; }

    class Timer;
    inline std::vector<Timer*>& active() { static std::vector<Timer*> a; return a; }

    inline void count(const std::string& name, size_t n = 1) { counters()[name] += n; }

    inline double elapsed(Clock::time_point t0)
    {
      return std::chrono::duration<double>(Clock::now() - t0).count();
    }

    // accumulates the lifetime of the object under `name`; timers still alive when the
    // report is printed (e.g., the program called exit()) are closed by the report
    class Timer
    {
      public:
        Timer(const std::string& _name) : name(_name), t0(Clock::now()) { active().push_back(this); }
        ~Timer()
        {
          auto it = std::find(active().rbegin(), active().rend(), this);
          if (it == active().rend()) return;   // already closed by report()
          active().erase(std::next(it).base());
          close();
        }
        void close()
        {
          Stat& s = timers()[name];
          s.calls++;
          s.secs += elapsed(t0);
        }
      private:
        std::string name;
        Clock::time_point t0;
    };

    inline void report()
    {
      if (!enabled()) return;
      double total = elapsed(startTime());
      for (auto t : active()) t->close();
      active().clear();

      std::vector<std::pair<std::string, Stat>> ts(timers().begin(), timers().end());
      std::sort(ts.begin(), ts.end(), [](const std::pair<std::string, Stat>& a,
                                         const std::pair<std::string, Stat>& b)
                                         { return a.second.secs > b.second.secs; });

      fprintf(stderr, "\n== profile (wall time %.3fs)\n", total);
      fprintf(stderr, "%-52s %10s %12s %12s %8s\n", "timer", "calls", "total s", "avg ms", "% wall");
      for (auto& t : ts)
        fprintf(stderr, "%-52s %10zu %12.3f %12.3f %7.1f%%\n", t.first.c_str(), t.second.calls,
                t.second.secs, 1000 * t.second.secs / t.second.calls, 100 * t.second.secs / total);

      fprintf(stderr, "%-52s %10s\n", "counter", "value");
      for (auto& c : counters())
        fprintf(stderr, "%-52s %10zu\n", c.first.c_str(), c.second);
      fflush(stderr);
    }

    // starts the wall clock and prints the report on exit (also on exit() calls)
    inline void init(bool enable)
    {
      enabled() = enable;
      startTime() = Clock::now();
      timers(); counters(); active();   // construct before registering, so they outlive report()
      atexit(report);
    }
  }
}

#endif

#include <gmpxx.h>
#include <stdio.h>
#include <algorithm>
#include <map>
#include <mutex>
#include <thread>
#include <random>
#include <cmath>

#ifdef HALFDELTA
#  define INC 2
#else
#  define INC 1
#endif

static constexpr int THREADS = 14;

namespace {

struct Point {
    mpz_class x;
    mpz_class y;

    template<typename F, typename G>
    explicit Point(F&& ff, G&& gg) : x(std::forward<F>(ff)), y(std::forward<G>(gg)) {}

    Point() : x(0), y(0) {}

    Point(const Point& a) : x(a.x), y(a.y) {}
    Point(Point&& a) : x(std::move(a.x)), y(std::move(a.y)) {}

    Point& operator=(const Point& a) { x = a.x; y = a.y; return *this; }
    Point& operator=(Point&& a) { x = std::move(a.x); y = std::move(a.y); return *this; }

    friend int cmp(const Point& a, const Point& b) {
        int fc = cmp(a.x, b.x);
        if (fc) return fc;
        return cmp(a.y, b.y);
    }

    friend bool operator<(const Point& a, const Point& b) { return cmp(a, b) < 0; }
    friend bool operator>(const Point& a, const Point& b) { return cmp(a, b) > 0; }
    friend bool operator<=(const Point& a, const Point& b) { return cmp(a, b) <= 0; }
    friend bool operator>=(const Point& a, const Point& b) { return cmp(a, b) >= 0; }
    friend bool operator==(const Point& a, const Point& b) { return a.x == b.x && a.y == b.y; }
    friend bool operator!=(const Point& a, const Point& b) { return a.x != b.x || a.y != b.y; }

    std::string to_string() const { return "(" + x.get_str() + ", " + y.get_str() + ")"; }
};

int Turn(const Point& o, const Point& a, const Point& b, mpz_class& tmp1, mpz_class& tmp2, mpz_class& tmp3) {
    tmp1 = a.x - o.x;
    tmp2 = b.y - o.y;
    tmp1 *= tmp2;
    tmp2 = a.y - o.y;
    tmp3 = b.x - o.x;
    tmp2 *= tmp3;
    return cmp(tmp1, tmp2);
}

void MakeHull(std::vector<Point>& points, mpz_class& tmp1, mpz_class& tmp2, mpz_class& tmp3) {
    if (points.size() <= 1) return;
    std::sort(points.begin(), points.end());
    std::vector<Point> ret;
    ret.reserve(points.size() + 1);
    ret.push_back(points[0]);
    for (auto it = points.begin() + 1; it != points.end(); ++it) {
        while (ret.size() >= 2 && Turn(*(ret.end() - 2), *(ret.end() - 1), *it, tmp1, tmp2, tmp3) <= 0) {
            ret.pop_back();
        }
        if (*it != ret.back()) {
            ret.push_back(*it);
        }
    }
    if (ret.size() == 1) {
        points = std::move(ret);
        return;
    }
    ret.pop_back();
    size_t lower_size = ret.size();
    ret.push_back(*points.rbegin());
    for (auto it = points.rbegin() + 1; it != points.rend(); ++it) {
        while (ret.size() >= 2 + lower_size && Turn(*(ret.end() - 2), *(ret.end() - 1), *it, tmp1, tmp2, tmp3) <= 0) {
            ret.pop_back();
        }
        if (*it != ret.back()) {
            ret.push_back(*it);
        }
    }
    ret.pop_back();
    points = std::move(ret);
}

struct HullData {
    std::vector<Point> points;
    mpz_class max_abs_g;

    std::string to_string() const {
        std::string ret = "[[";
        for (size_t i = 0; i < points.size(); ++i) {
            if (i) ret += ", ";
            ret += points[i].to_string();
        }
        ret += "], " + max_abs_g.get_str() + "]";
        return ret;
    }
};

bool ProcessHull(HullData& out, const std::map<int, HullData>& in, int delta, mpz_class& tmp1, mpz_class& tmp2, mpz_class& tmp3) {
    out.points.clear();
    const mpz_class* max_parent_abs_g_ptr = nullptr;
    std::map<int, HullData>::const_iterator it;
    if (INC - delta > 0 && (it = in.find(INC - delta), it != in.end())) {
        max_parent_abs_g_ptr = &it->second.max_abs_g;
        for (const Point& point : it->second.points) {
            out.points.emplace_back(point.y << 1, point.y - point.x);
        }
    }
    if ((it = in.find(delta - INC), it != in.end())) {
        if (max_parent_abs_g_ptr == nullptr || it->second.max_abs_g > *max_parent_abs_g_ptr) {
            max_parent_abs_g_ptr = &it->second.max_abs_g;
        }
        for (const Point& point : it->second.points) {
            out.points.emplace_back(point.x << 1, point.y);
        }
        if (delta - INC <= 0) {
            for (const Point& point : it->second.points) {
                out.points.emplace_back(point.x << 1, point.x + point.y);
            }
        }
    }
    if (out.points.size() == 0) return false;
    MakeHull(out.points, tmp1, tmp2, tmp3);
    mpz_class max_parent_abs_g = (*max_parent_abs_g_ptr) << 1;
    const mpz_class* min_g_ptr = nullptr;
    const mpz_class* max_g_ptr = nullptr;
    for (const auto& entry : out.points) {
        if (min_g_ptr == nullptr || entry.y < *min_g_ptr) min_g_ptr = &entry.y;
        if (max_g_ptr == nullptr || entry.y > *max_g_ptr) max_g_ptr = &entry.y;
    }
    mpz_class abs_min_g = abs(*min_g_ptr), abs_max_g = abs(*max_g_ptr);
    if (abs_min_g > abs_max_g) abs_max_g = std::move(abs_min_g);
    if (max_parent_abs_g < abs_max_g) {
        out.max_abs_g = std::move(max_parent_abs_g);
    } else {
        out.max_abs_g = std::move(abs_max_g);
    }
    return true;
}

void ProcessDivStep(std::map<int, HullData>& new_state, const std::map<int, HullData>& old_state, int step) {
    std::vector<int> new_deltas;
    int min_new_delta = std::min({INC + old_state.begin()->first, INC - old_state.begin()->first, INC + old_state.rbegin()->first, INC - old_state.rbegin()->first});
    int max_new_delta = std::max({INC + old_state.begin()->first, INC - old_state.begin()->first, INC + old_state.rbegin()->first, INC - old_state.rbegin()->first});
    for (int new_delta = min_new_delta; new_delta <= max_new_delta; new_delta += 2) {
        new_deltas.push_back(new_delta);
    }
    new_state.clear();
    std::random_device rng;
    std::mutex mutex;
    std::vector<std::thread> threads;
    for (int t = 0; t < THREADS; ++t) {
        threads.emplace_back([&](){
            mpz_class tmp1, tmp2, tmp3;
            while (true) {
                std::vector<int> deltas;
                std::map<int, HullData> new_hulls;
                {
                    std::unique_lock<std::mutex> lock(mutex);
                    if (new_deltas.empty()) return;
                    int count = std::max<int>(std::min<int>(new_deltas.size() / (2 * THREADS), 100000000 / ((step + 1) * (step + 1))), 1);
                    while (count--) {
                        std::swap(new_deltas.back(), new_deltas[std::uniform_int_distribution<size_t>(0, new_deltas.size() - 1)(rng)]);
                        deltas.push_back(new_deltas.back());
                        new_deltas.pop_back();
                    }
                }
                for (int delta : deltas) {
                    HullData new_hull;
                    if (ProcessHull(new_hull, old_state, delta, tmp1, tmp2, tmp3)) {
                        new_hulls[delta] = std::move(new_hull);
                    }
                }
                {
                    std::unique_lock<std::mutex> lock(mutex);
                    for (auto& item : new_hulls) {
                        new_state[item.first] = std::move(item.second);
                    }
                }
            }
        });
    }
    for (auto& thread : threads) thread.join();
}

mpz_class MaxAbsG(const std::map<int, HullData>& state) {
    const mpz_class* max_abs_g_ptr = nullptr;
    for (const auto& item : state) {
        if (max_abs_g_ptr == nullptr || (item.second.max_abs_g > *max_abs_g_ptr)) max_abs_g_ptr = &item.second.max_abs_g;
    }
    return *max_abs_g_ptr;
}

}

int main() {
    setbuf(stdout, nullptr);
    std::map<int, HullData> state;
    state[1].points = std::vector<Point>{Point{0,0},Point{1,0},Point{1,1}};
    state[1].max_abs_g = 1;
    int steps = 0;
    while (true) {
        std::map<int, HullData> new_state;
        ProcessDivStep(new_state, state, steps);
        state = std::move(new_state);
        ++steps;
        mpz_class max_abs_g = MaxAbsG(state);
        mpz_class alpha = ((mpz_class{1} << steps) - 1) / max_abs_g;
        int shift = std::max<int>(0, mpz_sizeinbase(alpha.get_mpz_t(), 2) - 128);
        mpz_class shifted_alpha = alpha >> shift;
        printf("%i 0x%s (2**%f)\n", steps, alpha.get_str(16).c_str(), log2(shifted_alpha.get_d()) + shift);
    }
    return 0;
}

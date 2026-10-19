// Invented shapes for a lexer to read.
#include <vector>
#include <string>

namespace geo {

/** A point on a plane. */
struct Point {
    double x = 0.0, y = 0.0;
};

template <typename T>
concept Measured = requires(T t) { t.area(); };

class Shape {
public:
    virtual ~Shape() = default;
    [[nodiscard]] virtual double area() const noexcept = 0;
protected:
    std::string name_{"shape"};
};

/// A circle of some radius.
class Circle final : public Shape {
public:
    explicit Circle(double r) : r_(r) {}
    double area() const noexcept override { return 3.14159 * r_ * r_; }
private:
    double r_;
};

enum class Hue : unsigned char { Red, Green = 4, Blue };

auto total(const std::vector<Circle>& cs) -> double {
    double sum{};
    for (const auto& c : cs) sum += c.area();
    return sum;
}

}  // namespace geo

int main() {
    using namespace geo;
    auto twice = [](int v) constexpr { return v * 2; };
    const char* raw = R"tag(a "quoted" \n line)tag";
    char16_t wide = u'x';
    std::vector<Circle> cs{Circle{1.5}, Circle{2.0}};
    static_assert(sizeof(int) >= 2, "ints are wide enough");
    return twice(static_cast<int>(total(cs))) > 0x10 ? 0 : 1;
}

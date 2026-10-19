// leantex: formats = html
#include <vector>

namespace gauge {

//! A shelf of invented levels.
class Shelf {
public:
    /// Adds a level.
    void add(int level) { levels_.push_back(level); }
private:
    std::vector<int> levels_;
};

}  // namespace gauge

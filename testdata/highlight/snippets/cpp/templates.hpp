#pragma once
#include <cstddef>
namespace store::detail {
template <class Key, class Value, std::size_t N = 8>
class Shelf {
  public:
    using size_type = std::size_t;
    constexpr size_type capacity() const { return N; }
    Value& operator[](const Key& k);
    friend bool operator==(const Shelf&, const Shelf&) = default;
  private:
    alignas(16) Value slots_[N]{};
};
template <class K, class V, std::size_t N>
V& Shelf<K, V, N>::operator[](const K& k) { return slots_[k % N]; }
inline namespace v2 { int version() { return 2'0; } }
}

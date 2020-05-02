//
// Implementation of C++17 std::any with configurable small object-size
// optimization Only For C++17 compilers. Drop-In replacement for std::any
//
// See also:
//   + http://en.cppreference.com/w/cpp/any
//   + http://en.cppreference.com/w/cpp/experimental/any
//   + http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2015/n4562.html#any
//   + https://cplusplus.github.io/LWG/lwg-active.html#2509
//
//
// Copyright (c) 2016 Denilson das Mercês Amorim
// Copyright (c) 2020 Harikrishnan
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
//
#ifndef NONSTD_ANY_HPP
#define NONSTD_ANY_HPP
#pragma once
#include <type_traits>
#include <typeinfo>
#include <utility>

// you can opt-out of exceptions by definining ANY_IMPL_NO_EXCEPTIONS,
// but you must ensure not to cast badly when passing an `any' object to
// any_cast<T>(any)

// you can opt-out of RTTI by defining ANY_IMPL_NO_RTTI,
// in order to disable functions working with the typeid of a type

namespace nonstd {
class bad_any_cast : public std::bad_cast {
public:
  const char *what() const noexcept override { return "bad any cast"; }
};

template <std::size_t StackStorageSize = 3 * sizeof(void *),
          std::size_t Align = alignof(void *)>
class basic_any {
public:
  /// Exported to help observers from outside
  static constexpr auto STACK_STORAGE_SIZE = StackStorageSize;
  static constexpr auto ALIGNMENT = Align;

  /// Constructs an object of type basic_any with an empty state.
  basic_any() = default;

  /// Constructs an object of type basic_any with an equivalent state as other.
  basic_any(const basic_any &rhs) : vtable(rhs.vtable) {
    if (rhs.has_value())
      rhs.vtable->copy(rhs.storage, this->storage);
  }

  /// Constructs an object of type basic_any with a state equivalent to the
  /// original state of other. rhs is left in a valid but otherwise unspecified
  /// state.
  basic_any(basic_any &&rhs) noexcept : vtable(rhs.vtable) {
    if (rhs.has_value()) {
      rhs.vtable->move(rhs.storage, this->storage);
      rhs.vtable = nullptr;
    }
  }

  /// Same effect as this->reset().
  ~basic_any() { this->reset(); }

  /// Constructs an object of type basic_any that contains an object of type T
  /// direct-initialized with std::forward<ValueType>(value).
  ///
  /// T shall satisfy the CopyConstructible requirements, otherwise the program
  /// is ill-formed. This is because an `basic_any` may be copy constructed into
  /// another `basic_any` at anytime, so a copy should always be allowed.
  template <typename ValueType,
            typename = typename std::enable_if_t<
                !std::is_same_v<typename std::decay_t<ValueType>, basic_any>>>
  basic_any(ValueType &&value) { // NOLINT(hicpp-explicit-conversions) -
                                 // Required by standard
    static_assert(
        std::is_copy_constructible_v<typename std::decay_t<ValueType>>,
        "T shall satisfy the CopyConstructible requirements.");
    this->construct(std::forward<ValueType>(value));
  }

  /// Constructs an `basic_any` object with a "contained object" of the decayed
  /// type of `T`, which is initialized via `std::forward<T>(value)`.
  template <
      typename T, typename... Args, typename VT = std::decay_t<T>,
      std::enable_if_t<std::conjunction_v<std::is_copy_constructible<VT>,
                                          std::is_constructible<VT, Args...>>>
          * = nullptr>
  explicit basic_any(std::in_place_type_t<T> /*tag*/, Args &&... args) {
    this->construct<VT>(std::forward<Args>(args)...);
  }

  /// Constructs an `basic_any` object with a "contained object" of the passed
  /// type `VT` as a decayed type of `T`. `VT` is initialized as if
  /// direct-non-list-initializing an object of type `VT` with the arguments
  /// `initializer_list, std::forward<Args>(args)...`.
  template <typename T, typename U, typename... Args,
            typename VT = std::decay_t<T>,
            std::enable_if_t<std::conjunction_v<
                std::is_copy_constructible<VT>,
                std::is_constructible<VT, std::initializer_list<U> &, Args...>>>
                * = nullptr>
  explicit basic_any(std::in_place_type_t<T> /*tag*/,
                     std::initializer_list<U> ilist, Args &&... args) {
    this->construct<VT>(ilist, std::forward<Args>(args)...);
  }

  /// Has the same effect as basic_any(rhs).swap(*this). No effects if an
  /// exception is thrown.
  auto operator=(const basic_any &rhs) -> basic_any & {
    basic_any(rhs).swap(*this);
    return *this;
  }

  /// Has the same effect as basic_any(std::move(rhs)).swap(*this).
  ///
  /// The state of *this is equivalent to the original state of rhs and rhs is
  /// left in a valid but otherwise unspecified state.
  auto operator=(basic_any &&rhs) noexcept -> basic_any & {
    basic_any(std::move(rhs)).swap(*this);
    return *this;
  }

  /// Has the same effect as
  /// basic_any(std::forward<ValueType>(value)).swap(*this). No effect if a
  /// exception is thrown.
  ///
  /// T shall satisfy the CopyConstructible requirements, otherwise the program
  /// is ill-formed. This is because an `basic_any` may be copy constructed into
  /// another `basic_any` at basic_any time, so a copy should always be allowed.
  template <typename ValueType,
            typename = typename std::enable_if_t<
                !std::is_same_v<typename std::decay_t<ValueType>, basic_any>>>
  auto operator=(ValueType &&value) -> basic_any & {
    static_assert(
        std::is_copy_constructible_v<typename std::decay_t<ValueType>>,
        "T shall satisfy the CopyConstructible requirements.");
    basic_any(std::forward<ValueType>(value)).swap(*this);
    return *this;
  }

  // Modifiers

  /// basic_any::emplace()
  ///
  /// Emplaces a value within an `basic_any` object by calling
  /// `basic_any::reset()`, initializing the contained value as if
  /// direct-non-list-initializing an object of type `VT` with the arguments
  /// `std::forward<Args>(args)...`, and returning a reference to the new
  /// contained value.
  ///
  /// Note: If an exception is thrown during the call to `VT`'s constructor,
  /// `*this` does not contain a value, and any previously contained value has
  /// been destroyed.
  template <typename T, typename... Args, typename VT = std::decay_t<T>,
            std::enable_if_t<std::is_copy_constructible_v<VT> &&
                             std::is_constructible_v<VT, Args...>> * = nullptr>
  auto emplace(Args &&... args) -> VT & {
    reset(); // NOTE: reset() is required here even in the world of exceptions.
    this->construct<VT>(std::forward<Args>(args)...);
    return *cast<VT>();
  }

  /// Overload of `basic_any::emplace()` to emplace a value within an
  /// `basic_any` object by calling `basic_any::reset()`, initializing the
  /// contained value as if direct-non-list-initializing an object of type `VT`
  /// with the arguments `initializer_list, std::forward<Args>(args)...`, and
  /// returning a reference to the new contained value.
  ///
  /// Note: If an exception is thrown during the call to `VT`'s constructor,
  /// `*this` does not contain a value, and any previously contained value has
  /// been destroyed. The function shall not participate in overload resolution
  /// unless `is_copy_constructible_v<VT>` is `true` and
  /// `is_constructible_v<VT, initializer_list<U>&, Args...>` is `true`.
  template <
      typename T, typename U, typename... Args, typename VT = std::decay_t<T>,
      std::enable_if_t<std::is_copy_constructible_v<VT> &&
                       std::is_constructible_v<VT, std::initializer_list<U> &,
                                               Args...>> * = nullptr>
  auto emplace(std::initializer_list<U> ilist, Args &&... args) -> VT & {
    reset(); // NOTE: reset() is required here even in the world of exceptions.
    this->construct<VT>(ilist, std::forward<Args>(args)...);
    return *cast<VT>();
  }

  /// If not empty, destroys the contained object.
  void reset() noexcept {
    if (has_value()) {
      this->vtable->destroy(storage);
      this->vtable = nullptr;
    }
  }

  /// Returns true if *this contains an object, otherwise false.
  [[nodiscard]] constexpr auto has_value() const noexcept -> bool {
    return this->vtable != nullptr;
  }

  /// Returns true if *this contains an object of Type `T`, otherwise false.
  template <typename T>
  [[nodiscard]] constexpr auto has_type() const noexcept -> bool {
    return has_value() && vtable == vtable_for_type<T>();
  }

#ifndef ANY_IMPL_NO_RTTI
  /// If *this has a contained object of type T, typeid(T); otherwise
  /// typeid(void).
  [[nodiscard]] constexpr auto type() const noexcept -> const std::type_info & {
    return has_value() ? this->vtable->type() : typeid(void);
  }
#endif

  /// Exchange the states of *this and rhs.
  void swap(basic_any &rhs) noexcept {
    if (this->vtable != rhs.vtable) {
      basic_any tmp(std::move(rhs));

      // move from *this to rhs.
      rhs.vtable =
          this->vtable; // NOLINT(bugprone-use-after-move,hicpp-invalid-access-moved)
      if (this->vtable != nullptr) {
        this->vtable->move(this->storage, rhs.storage);
        // this->vtable = nullptr; -- unneeded, see below
      }

      // move from tmp (previously rhs) to *this.
      this->vtable = tmp.vtable;
      if (tmp.vtable != nullptr) {
        tmp.vtable->move(tmp.storage, this->storage);
        tmp.vtable = nullptr;
      }
    } else {
      // same types
      if (this->vtable != nullptr)
        this->vtable->swap(this->storage, rhs.storage);
    }
  }

private: // Storage and Virtual Method Table
  union storage_union {
    using stack_storage_t =
        typename std::aligned_storage_t<StackStorageSize, Align>;

    void *dynamic;
    stack_storage_t
        stack; // default 3 words for e.g. std::string with SSO enabled
  };

  /// Base VTable specification.
  struct vtable_type {
    // Note: The caller is responssible for doing .vtable = nullptr after
    // destructful operations such as destroy() and/or move().

#ifndef ANY_IMPL_NO_RTTI
    /// The type of the object this vtable is for.
    const std::type_info &(*type)() noexcept;
#endif

    /// Destroys the object in the union.
    /// The state of the union after this call is unspecified, caller must
    /// ensure not to use src anymore.
    void (*destroy)(storage_union &) noexcept;

    /// Copies the **inner** content of the src union into the yet unitialized
    /// dest union. As such, both inner objects will have the same state, but on
    /// separate memory locations.
    void (*copy)(const storage_union &src, storage_union &dest);

    /// Moves the storage from src to the yet unitialized dest union.
    /// The state of src after this call is unspecified, caller must ensure not
    /// to use src anymore.
    void (*move)(storage_union &src, storage_union &dest) noexcept;

    /// Exchanges the storage between lhs and rhs.
    void (*swap)(storage_union &lhs, storage_union &rhs) noexcept;
  };

  /// VTable for dynamically allocated storage.
  template <typename T> struct vtable_dynamic {
#ifndef ANY_IMPL_NO_RTTI
    static auto type() noexcept -> const std::type_info & { return typeid(T); }
#endif

    static void destroy(storage_union &storage) noexcept {
      // assert(reinterpret_cast<T*>(storage.dynamic));
      delete reinterpret_cast<T *>(storage.dynamic); // NOLINT
    }

    static void copy(const storage_union &src, storage_union &dest) {
      dest.dynamic = new T(*reinterpret_cast<const T *>(src.dynamic)); // NOLINT
    }

    static void move(storage_union &src, storage_union &dest) noexcept {
      dest.dynamic = src.dynamic;
      src.dynamic = nullptr;
    }

    static void swap(storage_union &lhs, storage_union &rhs) noexcept {
      // just exchage the storage pointers.
      std::swap(lhs.dynamic, rhs.dynamic);
    }
  };

  /// VTable for stack allocated storage.
  template <typename T> struct vtable_stack {
#ifndef ANY_IMPL_NO_RTTI
    static auto type() noexcept -> const std::type_info & { return typeid(T); }
#endif

    static void destroy(storage_union &storage) noexcept {
      reinterpret_cast<T *>(&storage.stack)->~T();
    }

    static void copy(const storage_union &src, storage_union &dest) {
      new (&dest.stack) T(reinterpret_cast<const T &>(src.stack));
    }

    static void move(storage_union &src, storage_union &dest) noexcept {
      // one of the conditions for using vtable_stack is a nothrow move
      // constructor, so this move constructor will never throw a exception.
      new (&dest.stack) T(std::move(reinterpret_cast<T &>(src.stack)));
      destroy(src);
    }

    static void swap(storage_union &lhs, storage_union &rhs) noexcept {
      storage_union tmp_storage;
      move(rhs, tmp_storage);
      move(lhs, rhs);
      move(tmp_storage, lhs);
    }
  };

  /// Whether the type T must be dynamically allocated or can be stored on the
  /// stack.
  template <typename T>
  static constexpr auto requires_allocation_v =
      !(std::is_nothrow_move_constructible_v<T> // N4562 §6.3/3
                                                // [basic_any.class]
        && sizeof(T) <= sizeof(storage_union::stack) &&
        std::alignment_of_v<T> <=
            std::alignment_of_v<typename storage_union::stack_storage_t>);

  /// Returns the pointer to the vtable of the type T.
  template <typename T> static auto vtable_for_type() -> vtable_type * {
    using VTableType =
        typename std::conditional_t<requires_allocation_v<T>, vtable_dynamic<T>,
                                    vtable_stack<T>>;
    static vtable_type table = {
#ifndef ANY_IMPL_NO_RTTI
        VTableType::type,
#endif
        VTableType::destroy, VTableType::copy,
        VTableType::move,    VTableType::swap,
    };
    return &table;
  }

protected:
  template <typename T, std::size_t StackStorageSize1, std::size_t Align1>
  friend auto
  any_cast(const basic_any<StackStorageSize1, Align1> *operand) noexcept
      -> const T *;
  template <typename T, std::size_t StackStorageSize1, std::size_t Align1>
  friend auto any_cast(basic_any<StackStorageSize1, Align1> *operand) noexcept
      -> T *;

  /// Casts (with no type_info checks) the storage pointer as const T*.
  template <typename T> constexpr auto cast() const noexcept -> const T * {
    if constexpr (requires_allocation_v<typename std::decay_t<T>>) {
      return reinterpret_cast<const T *>(storage.dynamic);
    } else {
      return reinterpret_cast<const T *>(&storage.stack);
    }
  }

  /// Casts (with no type_info checks) the storage pointer as T*.
  template <typename T> constexpr auto cast() noexcept -> T * {
    if constexpr (requires_allocation_v<typename std::decay_t<T>>) {
      return reinterpret_cast<T *>(storage.dynamic);
    } else {
      return reinterpret_cast<T *>(&storage.stack);
    }
  }

private:
  storage_union storage; // on offset(0) so no padding for align
  const vtable_type *vtable = nullptr;

  /// Chooses between stack and dynamic allocation for the type
  /// decay_t<ValueType>, assigns the correct vtable, and constructs the object
  /// on our storage.
  template <typename ValueType> void construct(ValueType &&value) {
    using T = typename std::decay_t<ValueType>;

    this->vtable = basic_any::vtable_for_type<T>();
    if constexpr (requires_allocation_v<T>) {
      storage.dynamic = new T(std::forward<ValueType>(value)); // NOLINT
    } else {
      new (&storage.stack) T(std::forward<ValueType>(value));
    }
  }
  template <typename T, typename... Args> void construct(Args &&... args) {
    this->vtable = basic_any::vtable_for_type<T>();
    if constexpr (requires_allocation_v<T>) {
      storage.dynamic = new T(std::forward<Args>(args)...); // NOLINT
    } else {
      new (&storage.stack) T(std::forward<Args>(args)...);
    }
  }
  template <typename T, typename U, typename... Args>
  void construct(std::initializer_list<U> ilist, Args &&... args) {
    this->vtable = basic_any::vtable_for_type<T>();
    if constexpr (requires_allocation_v<T>) {
      storage.dynamic = new T(ilist, std::forward<Args>(args)...); // NOLINT
    } else {
      new (&storage.stack) T(ilist, std::forward<Args>(args)...);
    }
  }
};

namespace detail {
[[noreturn]] inline void throw_bad_any_cast() {
#ifndef ANY_IMPL_NO_EXCEPTIONS
  throw bad_any_cast();
#endif
}
} // namespace detail

/// If operand != nullptr && operand->type() == typeid(ValueType), a pointer to
/// the object contained by operand, otherwise nullptr.
template <typename ValueType, std::size_t StackStorageSize, std::size_t Align>
inline auto any_cast(const basic_any<StackStorageSize, Align> *operand) noexcept
    -> const ValueType * {
  using T = typename std::decay_t<ValueType>;

  if (operand &&
      operand->vtable ==
          basic_any<StackStorageSize, Align>::template vtable_for_type<T>())
    return operand->template cast<T>();
  return nullptr;
}

/// If operand != nullptr && operand->type() == typeid(ValueType), a pointer to
/// the object contained by operand, otherwise nullptr.
template <typename ValueType, std::size_t StackStorageSize, std::size_t Align>
inline auto any_cast(basic_any<StackStorageSize, Align> *operand) noexcept
    -> ValueType * {
  using T = typename std::decay_t<ValueType>;

  if (operand &&
      operand->vtable ==
          basic_any<StackStorageSize, Align>::template vtable_for_type<T>())
    return operand->template cast<T>();
  return nullptr;
}

/// Performs *any_cast<add_const_t<remove_reference_t<ValueType>>>(&operand), or
/// throws bad_any_cast on failure.
template <typename ValueType, std::size_t StackStorageSize, std::size_t Align>
inline auto any_cast(const basic_any<StackStorageSize, Align> &operand)
    -> ValueType {
  using U =
      typename std::remove_cv_t<typename std::remove_reference_t<ValueType>>;
  static_assert(std::is_constructible_v<ValueType, const U &>,
                "Invalid ValueType");

  if (auto p = any_cast<U>(&operand))
    return static_cast<ValueType>(*p);

  detail::throw_bad_any_cast();
}

/// Performs *any_cast<remove_reference_t<ValueType>>(&operand), or throws
/// bad_any_cast on failure.
template <typename ValueType, std::size_t StackStorageSize, std::size_t Align>
inline auto any_cast(basic_any<StackStorageSize, Align> &operand) -> ValueType {
  using U =
      typename std::remove_cv_t<typename std::remove_reference_t<ValueType>>;
  static_assert(std::is_constructible_v<ValueType, U &>, "Invalid ValueType");

  if (auto p = any_cast<U>(&operand))
    return static_cast<ValueType>(*p);
  detail::throw_bad_any_cast();
}

///
/// If ValueType is MoveConstructible and isn't a lvalue reference, performs
/// std::move(*any_cast<remove_reference_t<ValueType>>(&operand)), otherwise
/// *any_cast<remove_reference_t<ValueType>>(&operand). Throws bad_any_cast on
/// failure.
///
template <typename ValueType, std::size_t StackStorageSize, std::size_t Align>
inline auto any_cast(basic_any<StackStorageSize, Align> &&operand)
    -> ValueType {
  using U =
      typename std::remove_cv_t<typename std::remove_reference_t<ValueType>>;
  static_assert(std::is_constructible_v<ValueType, U>, "Invalid ValueType");
  return static_cast<ValueType>(std::move(any_cast<U &>(operand)));
}

template <typename T, typename... Args> auto make_any(Args &&... args) {
  return basic_any(std::in_place_type_t<T>(), std::forward<Args>(args)...);
}

template <typename T, typename U, typename... Args>
auto make_any(std::initializer_list<U> il, Args &&... args) {
  return basic_any(std::in_place_type_t<T>(), il, std::forward<Args>(args)...);
}

template <std::size_t StackStorageSize, std::size_t Align, typename T,
          typename... Args>
auto make_any_with(Args &&... args) {
  return basic_any<StackStorageSize, Align>(std::in_place_type_t<T>(),
                                            std::forward<Args>(args)...);
}

template <std::size_t StackStorageSize, std::size_t Align, typename T,
          typename U, typename... Args>
auto make_any_with(std::initializer_list<U> il, Args &&... args) {
  return basic_any<StackStorageSize, Align>(std::in_place_type_t<T>(), il,
                                            std::forward<Args>(args)...);
}

template <std::size_t StackStorageSize, std::size_t Align>
inline void swap(basic_any<StackStorageSize, Align> &lhs,
                 basic_any<StackStorageSize, Align> &rhs) noexcept {
  lhs.swap(rhs);
}

template <typename T, std::size_t StackStorageSize, std::size_t Align>
auto any_has_type(const basic_any<StackStorageSize, Align> &a) -> bool {
  return a.template has_type<T>();
}

using any = basic_any<>;
} // namespace nonstd
#endif

#include <iostream>

template<class T>
class Matrix {
 private:
  int __strings_count;
  int __columns_count;
  // TODO: replace to std::vector
  T** __matrix;

 public:
  Matrix(const Matrix<T>& matrix)
      : __strings_count(matrix.__strings_count), __columns_count(matrix.__columns_count) {
    __matrix = new T*[__strings_count];
    for (int i = 0; i < __strings_count; ++i) {
      __matrix[i] = new T[__columns_count];
      for (int j = 0; j < __columns_count; ++j) __matrix[i][j] = matrix.__matrix[i][j];
    }
  }

  Matrix(int strings_count, int columns_count)
      : __strings_count(strings_count), __columns_count(columns_count) {
    __matrix = new T*[strings_count];
    for (int i = 0; i < strings_count; ++i) __matrix[i] = new T[columns_count];
  }

  Matrix(int strings_count, int columns_count, T filler)
      : __strings_count(strings_count), __columns_count(columns_count) {
    __matrix = new T*[strings_count];
    const T zero = 0;
    for (int i = 0; i < strings_count; ++i) {
      __matrix[i] = new T[columns_count];
      for (int j = 0; j < columns_count; ++j) __matrix[i][j] = i == j ? filler : zero;
    }
  }

  ~Matrix() {
    for (int i = 0; i < __strings_count; ++i) delete[] __matrix[i];
    delete[] __matrix;
  }

  T det() {
    if (__strings_count != __columns_count) throw;

    Matrix<T> matrix(*this);
    bool odd_switched_rows = false;
    T det = 1;

    for (int i = 0; i < __strings_count; ++i) {
      bool found_non_zero = false;
      for (int j = i; j < __strings_count; ++j) {
        if (matrix.__matrix[j][i] != 0) {
          std::swap(matrix.__matrix[j], matrix.__matrix[i]);
          if (j != i) odd_switched_rows = !odd_switched_rows;
          found_non_zero = true;
          break;
        }
      }
      if (!found_non_zero) return 0;
      det *= matrix.__matrix[i][i];

      for (int m = i + 1; m < __strings_count; ++m) {
        T coeff = matrix.__matrix[m][i] / matrix.__matrix[i][i];
        for (int j = i; j < __columns_count; ++j) matrix.__matrix[m][j] -= matrix.__matrix[i][j] * coeff;
      }
    }

    return odd_switched_rows ? -det : det;
  }

  void pow(int degree) {
    if (degree < 0 || __strings_count != __columns_count) throw;

    Matrix<T> temp(__strings_count, __columns_count, 1);

    while (degree) {
      if (degree & 1) temp *= *this;
      *this *= *this;
      degree >>= 1;
    }

    T** tmp = __matrix;
    __matrix = temp.__matrix;
    temp.__matrix = tmp;
  }

 private:
  struct SimplexVar {
    char __name = 'x';
    int __number = 0;
    SimplexVar() = default;
    SimplexVar(SimplexVar&&) = default;
    void set(char name, int number) {
      __name = name;
      __number = number;
    }
    inline constexpr SimplexVar& operator=(SimplexVar&& v) = default;
    friend std::ostream& operator<<(std::ostream& out, const SimplexVar& v) {
      out << v.__name + std::to_string(v.__number);
      return out;
    }
  };
  SimplexVar* __strings_simplex_variables = nullptr;
  SimplexVar* __columns_simplex_variables = nullptr;

 public:
  void start_simplex_method() {
    __columns_simplex_variables = new SimplexVar[__columns_count];
    __strings_simplex_variables = new SimplexVar[__strings_count];
    for (int i = 0; i < __columns_count; ++i) __columns_simplex_variables[i].set('x', i);
    for (int i = 0; i < __strings_count; ++i) __strings_simplex_variables[i].set('y', i);
  }

  void end_simplex_method() {
    delete[] __strings_simplex_variables;
    delete[] __columns_simplex_variables;
    __strings_simplex_variables = nullptr;
    __columns_simplex_variables = nullptr;
  }

  /**
   * @brief Solves the canonical reduced linear programming problem
   *
   * Requires the following matrix starting with 2nd row and 2nd column:
   *
   *  B    1    x1   x2   ...   xn
   *  f    c0  -c1  -c2   ...  -cn
   *  y1   b1  a11  a12   ...  a1n
   *  y2   b2  a21  a22   ...  a2n
   *  ...  ...  ...  ...  ...  ...
   *  ym   bm  am1  am2   ...  amn
   *
   * for function f(x1, x2, ..., xn) = c0 + c1*x1 + c2*x2 + ... + cn*xn --> max
   * with the system of linear equations:
   *
   *  a11*x1 + a12*x2 + ... + a1n*xn + y1 = b1
   *  a21*x1 + a22*x2 + ... + a2n*xn + y2 = b2
   *  ...   ...   ...   ...   ...   ...   ...
   *  am1*x1 + am2*x2 + ... + amn*xn + ym = bm
   *
   * where (y1, y2, ..., ym) is a basis all of whose variables are non-negative!
   * b1, b2, ..., bm also are non-negative!
   *
   * @return 0 if f_max == matrix[0][0]
   *        -1 if f_max is undefined
   */
  int simplex_method_next_iterate() {
    // step 1
    int index_min_negative_element = 0;
    T min_negative_element = T(0LL);
    for (int i = 1; i < __columns_count; ++i) {
      if (__matrix[0][i] < min_negative_element) {
        min_negative_element = __matrix[0][i];
        index_min_negative_element = i;
      }
    }
    if (!index_min_negative_element) return 0;

    // step 2
    for (int q = 1; q < __columns_count; ++q) {
      bool not_found_negative_column = false;
      for (int i = 0; i < __strings_count; ++i) {
        if (__matrix[i][q] >= T(0LL)) {
          not_found_negative_column = true;
          break;
        }
      }
      if (!not_found_negative_column) return -1;
    }

    // step 3
    int q = __q = index_min_negative_element;

    // step 4
    int p = 0;
    T min_element;
    for (int i = 1; i < __strings_count; ++i) {
      if (__matrix[i][q] > T(0LL)) {
        T temp = __matrix[i][0] / __matrix[i][q];
        if (!p || temp < min_element) {
          min_element = std::move(temp);
          p = i;
        }
      }
    }
    __p = p;

    std::cout << std::endl << *this;

    // step 5
    std::swap(__strings_simplex_variables[p], __columns_simplex_variables[q]);

    for (int i = 0; i < __strings_count; ++i) {
      for (int j = 0; j < __columns_count; ++j) {
        if (i != p && j != q) { __matrix[i][j] -= __matrix[i][q] / __matrix[p][q] * __matrix[p][j]; }
      }
    }
    for (int i = 0; i < __strings_count; ++i) {
      if (i != p) { __matrix[i][q] /= -__matrix[p][q]; }
    }
    for (int j = 0; j < __columns_count; ++j) {
      if (j != q) { __matrix[p][j] /= __matrix[p][q]; }
    }
    __matrix[p][q] = T(1LL) / __matrix[p][q];

    __p = __q = 0;  // for coloring std::cout
    return 1;
  }

  /**
   * Like the simplex method above, but b1, b2, ..., bm can be negative.
   * One of c1, c2, ..., cn must be negative!
   */
  int dual_simplex_method_next_iterate() {
    // step 1
    int index_first_negative_element = 0;
    T first_negative_element = T(0LL);
    for (int i = 1; i < __strings_count; ++i) {
      if (__matrix[i][0] < first_negative_element) {
        first_negative_element = __matrix[i][0];
        index_first_negative_element = i;
        break;
      }
    }
    if (!index_first_negative_element) return 0;

    // step 2
    for (int p = 1; p < __strings_count; ++p) {
      if (__matrix[p][0] < T(0LL)) {
        bool all_positive = true;
        for (int j = 1; j < __columns_count; ++j) {
          if (__matrix[p][j] < T(0LL)) {
            all_positive = false;
            break;
          }
        }
        if (all_positive) return -1;
      }
    }

    // step 3
    int p = __p = index_first_negative_element;

    // step 4
    int q = 0;
    T max_element;
    for (int j = 1; j < __columns_count; ++j) {
      if (__matrix[p][j] < T(0LL)) {
        T temp = __matrix[0][j] / __matrix[p][j];
        if (!q || temp > max_element) {
          max_element = std::move(temp);
          q = j;
        }
      }
    }
    __q = q;

    std::cout << std::endl << *this;

    // step 5
    std::swap(__strings_simplex_variables[p], __columns_simplex_variables[q]);

    for (int i = 0; i < __strings_count; ++i) {
      for (int j = 0; j < __columns_count; ++j) {
        if (i != p && j != q) { __matrix[i][j] -= __matrix[i][q] / __matrix[p][q] * __matrix[p][j]; }
      }
    }
    for (int i = 0; i < __strings_count; ++i) {
      if (i != p) { __matrix[i][q] /= -__matrix[p][q]; }
    }
    for (int j = 0; j < __columns_count; ++j) {
      if (j != q) { __matrix[p][j] /= __matrix[p][q]; }
    }
    __matrix[p][q] = T(1LL) / __matrix[p][q];

    __p = __q = 0;  // for coloring std::cout
    return 1;
  }

  Matrix<T>& operator*=(const Matrix<T>& right) {
    if (this->__columns_count != right.__strings_count) throw;

    Matrix<T> temp(this->__strings_count, right.__columns_count, 0);

    for (int i = 0; i < this->__strings_count; ++i)
      for (int j = 0; j < right.__columns_count; ++j)
        for (int r = 0; r < this->__columns_count; ++r)
          temp.__matrix[i][j] += this->__matrix[i][r] * right.__matrix[r][j];

    this->__columns_count = right.__columns_count;

    T** tmp = this->__matrix;
    this->__matrix = temp.__matrix;
    temp.__matrix = tmp;
    return *this;
  }

  Matrix<T>& operator*=(const T right) {
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j) __matrix[i][j] *= right;
    return *this;
  }

  Matrix<T> operator*(const Matrix<T> right) {
    return Matrix<T>(*this) *= right;
  }

  Matrix<T> operator*(const T right) const {
    return Matrix<T>(*this) *= right;
  }

  Matrix<T>& operator=(const Matrix<T>& right) {
    if (this->__strings_count != right.__strings_count || this->__columns_count != right.__columns_count)
      throw std::invalid_argument("error: matrix sizes are not equal");
    for (int i = 0; i < this->__strings_count; ++i)
      for (int j = 0; j < this->__columns_count; ++j) this->__matrix[i][j] = right.__matrix[i][j];
    return *this;
  }

  Matrix<T>& operator=(const T right) {
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j) __matrix[i][j] = right;
    return *this;
  }

  Matrix<T>& operator+=(const Matrix<T>& right) {
    if (this->__strings_count != right.__strings_count || this->__columns_count != right.__columns_count)
      throw std::invalid_argument("error: matrix sizes are not equal");
    for (int i = 0; i < this->__strings_count; ++i)
      for (int j = 0; j < this->__columns_count; ++j) this->__matrix[i][j] += right.__matrix[i][j];
    return *this;
  }

  Matrix<T>& operator+=(const T right) {
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j) __matrix[i][j] += right;
    return *this;
  }

  Matrix<T> operator+(const Matrix<T> right) const {
    return Matrix<T>(*this) += right;
  }

  Matrix<T> operator+(const T right) const {
    return Matrix<T>(*this) += right;
  }

  Matrix<T> operator+() {
    return Matrix<T>(*this);
  }

  Matrix<T> operator-() {
    Matrix<T> temp(*this);
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j) temp.__matrix[i][j] = -temp.__matrix[i][j];
    return temp;
  }

  Matrix<T>& operator-=(const Matrix<T>& right) {
    return *(this += -right);
  }

  Matrix<T>& operator-=(const T right) {
    return *(this += -right);
  }

  Matrix<T> operator-(const Matrix<T> right) const {
    return Matrix<T>(*this) -= right;
  }

  Matrix<T> operator-(const T right) const {
    return Matrix<T>(*this) -= right;
  }

  bool operator==(const Matrix<T>& right) const {
    if (this->__strings_count != right.__strings_count || this->__columns_count != right.__columns_count)
      return false;
    for (int i = 0; i < this->__strings_count; ++i)
      for (int j = 0; j < this->__columns_count; ++j)
        if (this->__matrix[i][j] != right.__matrix[i][j]) return false;
    return true;
  }

  bool operator==(const T right) const {
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j)
        if (__matrix[i][j] != right) return false;
    return true;
  }

  bool operator!=(const Matrix<T>& right) const {
    return !(*this == right);
  }

  bool operator!=(const T right) const {
    return !(*this == right);
  }

  operator bool() const {
    const T zero = 0;
    for (int i = 0; i < __strings_count; ++i)
      for (int j = 0; j < __columns_count; ++j)
        if (__matrix[i][j] != zero) return true;
    return false;
  }

  T* operator[](int i) {
    return __matrix[i];
  }

  friend std::istream& operator>>(std::istream& in, Matrix& m) {
    for (int i = 0; i < m.__strings_count; ++i) {
      for (int j = 0; j < m.__columns_count; ++j) { in >> m[i][j]; }
    }
    return in;
  }

 private:
  int __p = 0;
  int __q = 0;  // selected element in simplex method (__matrix[p][q])

 public:
  friend std::ostream& operator<<(std::ostream& out, const Matrix& m) {
    out.setf(std::ios::left);

    out << "B   1      ";
    if (m.__columns_simplex_variables)
      for (int i = 1; i < m.__columns_count; ++i) {
        out.width(7);
        out << m.__columns_simplex_variables[i];
      }
    out << "\nf   ";

    for (int i = 0; i < m.__strings_count; ++i) {
      if (i != 0 && m.__strings_simplex_variables) out << m.__strings_simplex_variables[i] << "  ";

      for (int j = 0; j < m.__columns_count; ++j) {
        if (i == m.__p && j == m.__q) out << "\x1b[31m";
        out << m.__matrix[i][j];
        out << "\x1b[0m";
      }
      out << std::endl;
    }
    return out;
  }
};

// Represents a rational number (n/m) where 'n' is an integer and 'm' is a natural number
class Rational {
 private:
  long long n = 0;
  long long m = 1;

  inline constexpr long long __pow(long long a, int n) const noexcept {
    long long res = 1LL;
    while (n) {
      if (n & 1) res *= a;
      a *= a;
      n >>= 1;
    }
    return res;
  }

  /**
   * Find 'x' and 'y' for the equation: (a*x + b*y = gcd)
   *
   * @param a must be >= 0
   * @param b must be >= 0
   * @return the greatest common divisor
   */
  inline constexpr long long __gcd_extended(long long a,
                                            long long b,
                                            long long& x,
                                            long long& y) const noexcept {
    x = 1;
    y = 0;
    long long xx = 0, yy = 1;
    while (b) {
      long long c = a / b;
      std::swap(a, b);
      b %= a;
      std::swap(x, xx);
      xx -= x * c;
      std::swap(y, yy);
      yy -= y * c;
    }
    return a;
  }

  /**
   * @param a must be >= 0
   * @param b must be >= 0
   */
  inline constexpr long long __gcd(long long a, long long b) const noexcept {
    while (b) {
      std::swap(a, b);
      b %= a;
    }
    return a;
  }

  /**
   * @param m must be > 0
   */
  inline constexpr void __reduce(long long* n, long long* m) const {
    long long gcd = *n < 0 ? __gcd(-*n, *m) : __gcd(*n, *m);
    *n /= gcd;
    *m /= gcd;
  }

 public:
  /**
   * @param m must be > 0
   */
  Rational(long long n = 0LL, long long m = 1LL, bool reduce = true) {
    if (m <= 0) throw std::invalid_argument("error: n/m where m<=0");
    this->n = n;
    this->m = m;
    if (reduce) __reduce(&this->n, &this->m);
  }

  Rational(const Rational& r) {
    n = r.n;
    m = r.m;
  }

  Rational(Rational&& r) {
    n = std::move(r.n);
    m = std::move(r.m);
  }

  // numerator
  inline constexpr long long get_n() const {
    return n;
  }

  // denominator
  inline constexpr long long get_m() const {
    return m;
  }

  inline constexpr double get_value() const {
    return static_cast<double>(n) / static_cast<double>(m);
  }

  inline Rational operator*(const Rational& r) const {
    long long a = r.n;
    long long b = r.m;
    long long c = n;
    long long d = m;
    __reduce(&a, &d);
    __reduce(&c, &b);
    return Rational(std::move(a * c), std::move(b * d), false);
  }

  inline constexpr Rational& operator*=(const Rational& r) {
    long long a = r.n;
    long long b = r.m;
    __reduce(&a, &m);
    __reduce(&n, &b);
    n *= a;
    m *= b;
    return *this;
  }

  inline Rational operator/(const Rational& r) const {
    long long a = r.m;
    long long b = r.n;
    if (b < 0) a = -a, b = -b;
    long long c = n;
    long long d = m;
    __reduce(&a, &d);
    __reduce(&c, &b);
    return Rational(std::move(a * c), std::move(b * d), false);
  }

  inline constexpr Rational& operator/=(const Rational& r) {
    long long a = r.m;
    long long b = r.n;
    if (b < 0) a = -a, b = -b;
    __reduce(&a, &m);
    __reduce(&n, &b);
    n *= a;
    m *= b;
    return *this;
  }

  inline Rational operator+(const Rational& r) const {
    long long lcm = m * r.m / __gcd(m, r.m);
    return Rational(n * lcm / m + r.n * lcm / r.m, lcm);
  }

  inline constexpr Rational& operator+=(const Rational& r) {
    long long lcm = m * r.m / __gcd(m, r.m);
    n = n * lcm / m + r.n * lcm / r.m;
    m = lcm;
    __reduce(&n, &m);
    return *this;
  }

  inline Rational operator-() const {
    return Rational(-n, m);
  }

  inline Rational operator-(const Rational& r) const {
    long long lcm = m * r.m / __gcd(m, r.m);
    return Rational(n * lcm / m - r.n * lcm / r.m, lcm);
  }

  inline constexpr Rational& operator-=(const Rational& r) {
    long long lcm = m * r.m / __gcd(m, r.m);
    n = n * lcm / m - r.n * lcm / r.m;
    m = lcm;
    __reduce(&n, &m);
    return *this;
  }

  inline constexpr bool operator==(const Rational& r) const {
    return n == r.n && m == r.m;
  }

  inline constexpr bool operator!=(const Rational& r) const {
    return !(*this == r);
  }

  inline constexpr Rational& operator=(const Rational& r) {
    n = r.n;
    m = r.m;
    return *this;
  }

  inline constexpr Rational& operator=(Rational&& r) {
    n = std::move(r.n);
    m = std::move(r.m);
    return *this;
  }

  inline bool operator<(const Rational& r) const {
    return (*this - r).n < 0LL;
  }

  inline bool operator<=(const Rational& r) const {
    return (*this - r).n <= 0LL;
  }

  inline bool operator>(const Rational& r) const {
    return (*this - r).n > 0LL;
  }

  inline bool operator>=(const Rational& r) const {
    return (*this - r).n >= 0LL;
  }

  friend std::istream& operator>>(std::istream& in, Rational& r) {
    std::string s;
    in >> s;

    r.n = 0;
    std::size_t i = 0;
    bool is_negative = false;
    if (s[0] == '-') is_negative = true, ++i;
    while (i < s.size() && s[i] >= '0' && s[i] <= '9') r.n = r.n * 10 + s[i++] - 48;

    if (i == s.size())
      r.m = 1;
    else {
      ++i;
      r.m = 0;
      while (i < s.size() && s[i] >= '0' && s[i] <= '9') r.m = r.m * 10 + s[i++] - 48;
      r.__reduce(&r.n, &r.m);
    }

    if (is_negative) r.n = -r.n;

    return in;
  }

  friend std::ostream& operator<<(std::ostream& out, const Rational& r) {
    out.width(7);
    out.setf(std::ios::left);
    if (r.m != 1)
      out << std::to_string(r.n) + '/' + std::to_string(r.m);
    else
      out << r.n;
    return out;
  }
};

int main() {
  std::ios::sync_with_stdio(false);

  // int n, x;
  // std::cout << "Input n: ";
  // std::cin >> n >> x;
  // Matrix<double> A(n, x), J(n, n), T(n, n), b(n, 1);
  // for (int i = 0; i < n; ++i)
  //   for (int j = 0; j < x; ++j) std::cin >> A[i][j];

  // for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) std::cin >>
  // J[i][j]; for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) std::cin
  // >> T[i][j]; for (int i = 0; i < n; ++i) std::cin >> b[i][0]; A.Pow(5); A
  // *= b; if (A * T == T * J) std::cout << "YES";

  // std::cout << "Det: " << A.det() << std::endl;

  int n, m, x;
  std::cout << "1 - simplex\n2 - dual simplex\n";
  std::cin >> x;
  std::cout << "NxM: ";
  std::cin >> n >> m;
  std::cout << "matrix:\n";
  Matrix<Rational> S(n, m);
  std::cin >> S;

  S.start_simplex_method();
  switch (x) {
    case 1:
      while (S.simplex_method_next_iterate() == 1) {}
      break;
    case 2:
      while (S.dual_simplex_method_next_iterate() == 1) {}
      break;
    default:
      break;
  }
  std::cout << std::endl << S;
  S.end_simplex_method();

  return 0;
}

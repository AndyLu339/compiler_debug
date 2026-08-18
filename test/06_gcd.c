// 06_gcd.c — 辗转相除法求最大公约数
// 期望返回值: 6  (GCD(48, 18) = 6)

int gcd(int a, int b) {
  while (b != 0) {
    int t = a % b;
    a = b;
    b = t;
  }
  return a;
}

int main() {
  return gcd(48, 18);
}

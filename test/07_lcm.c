// 07_lcm.c — 最小公倍数 LCM
// 期望返回值: 36  (LCM(12, 18) = 36)

int gcd(int a, int b) {
  while (b != 0) {
    int t = a % b;
    a = b;
    b = t;
  }
  return a;
}

int lcm(int a, int b) {
  return a / gcd(a, b) * b;
}

int main() {
  return lcm(12, 18);
}

// 14_binary_gcd.c — Stein 二进制 GCD
// 期望返回值: 6  (BGCD(48, 18) = 6)
// 注意: ToyC 无位运算，用 /2 %2 替代

int bgcd(int a, int b) {
  if (a == 0)
    return b;
  if (b == 0)
    return a;
  int shift = 0;
  while (a % 2 == 0) {
    if (b % 2 == 0) {
      a = a / 2;
      b = b / 2;
      shift = shift + 1;
    } else {
      a = a / 2;
    }
  }
  while (b != 0) {
    while (b % 2 == 0)
      b = b / 2;
    if (a > b) {
      int t = a;
      a = b;
      b = t;
    }
    b = b - a;
  }
  int result = a;
  while (shift != 0) {
    result = result * 2;
    shift = shift - 1;
  }
  return result;
}

int main() {
  return bgcd(48, 18);
}

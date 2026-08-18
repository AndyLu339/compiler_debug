// 11_digit_sum.c — 各位数字之和
// 期望返回值: 15  (1 + 2 + 3 + 4 + 5 = 15)

int digit_sum(int n) {
  int sum = 0;
  while (n != 0) {
    sum = sum + n % 10;
    n = n / 10;
  }
  return sum;
}

int main() {
  return digit_sum(12345);
}

// 10_factorial.c — 阶乘（迭代）
// 期望返回值: 720  (6! = 720)

int fact(int n) {
  int result = 1;
  int i = 1;
  while (i <= n) {
    result = result * i;
    i = i + 1;
  }
  return result;
}

int main() {
  return fact(6);
}

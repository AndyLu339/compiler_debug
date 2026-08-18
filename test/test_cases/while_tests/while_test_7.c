int is_less_than_ten(int num) {
    return num < 10;
}
int main() {
    int i = 0;
    int sum = 0;
    while (is_less_than_ten(i)) {
        sum = sum + i;
        i = i + 1;
    }
    return sum;
}



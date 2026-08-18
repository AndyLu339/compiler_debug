int main() {
    int flag = 1;
    int i = 0;
    int sum = 0;
    while (flag) {
        sum = sum + i;
        i = i + 1;
        if (i == 3) {
            flag = 0;
        }
    }
    return sum;
}



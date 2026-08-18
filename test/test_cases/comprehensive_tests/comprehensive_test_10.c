
int main() {
    int i = 0;
    int sum = 0;
    while (i < 20) {
        i = i + 1;
        if (i % 3 == 0) {
            continue;
        }
        if (i > 15) {
            break;
        }
        sum = sum + i;
    }
    return sum;
}



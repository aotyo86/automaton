#include <stdio.h>
#include <regex.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int main() {
    regex_t preg;
    int result, match_count;
    regmatch_t pmatch[1];
    char *target = "aabaaababaaab"; // テスト対象の文字列
    int target_len = strlen(target);
    int offset = 0;
    clock_t start_time, end_time;

    // 正規表現のパターン
    const char *pattern = "(a|b)*a(a|b)";

    // 正規表現をコンパイル
    result = regcomp(&preg, pattern, REG_EXTENDED);
    if (result != 0) {
        printf("Failed to compile regex\n");
        return 1;
    }

    // 実行時間の測定開始
    start_time = clock();

    // パターンマッチング
    match_count = 0;
    while (offset < target_len && (result = regexec(&preg, target + offset, 1, pmatch, REG_NOTBOL)) == 0) {
        printf("Pattern match succeeded\n");
        printf("Match: %.*s\n", (int)(pmatch[0].rm_eo - pmatch[0].rm_so), target + offset + pmatch[0].rm_so);
        match_count++;
        offset += pmatch[0].rm_eo;
    }

    // 実行時間の測定終了
    end_time = clock();
    double elapsed_time = (double)(end_time - start_time) / CLOCKS_PER_SEC;

    // 結果の出力
    if (result != REG_NOMATCH && result != 0) {
        printf("Failed to execute regex\n");
        regfree(&preg);
        return 1;
    }

    printf("Total matches: %d\n", match_count);
    printf("Execution time: %.6f seconds\n", elapsed_time);

    // メモリの解放
    regfree(&preg);

    return 0;
}
#include<stdlib.h>
#include<stdio.h>
#include <iostream>
#include<string>
using namespace std;
string KEYWORD[15] = { "if","else","void","return","while","then","for","do","int","char","double","float","case","cin","cout" };
char SEPARATER[8] = { ';',',','{','}','[',']','(',')' };
char OPERATOR[8] = { '+','-','*','/','>','<','=','!' };
char FILTER[4] = { ' ','\t','\r','\n' };
const int IDENTIFIER = 100;
const int CONSTANT = 101;
const int FILTER_VALUE = 102;
bool IsKeyword(string word){
	for (int i = 0;i < 15;i++) {
		if (KEYWORD[i] == word)
			return true;
	}
	return false;

}
bool IsSeparater(char ch) {
	for (int i = 0;i < 8;i++) {
		if (SEPARATER[i] == ch)
			return true;
	}
	return false;

}
bool IsOperator(char ch) {
	for (int i = 0;i < 8;i++) {
		if (OPERATOR[i] == ch)
			return true;
	}
	return false;

}
bool IsFilter(char ch) {
	for (int i = 0;i< 4;i++) {
		if (FILTER[i] == ch)
			return true;
	}
	return false;

}
bool IsUpLetter(char ch) {
	if (ch >= 'A'&&ch <= 'Z') return true;
	return false;
}
bool IsLowLetter(char ch) {
	if (ch >= 'a'&&ch <= 'z') return true;
	return false;
}
bool IsDigit(char ch) {
	if (ch >= '0'&&ch <= '9') return true;
	return false;
}
template <class T>
int value(T*a, int n, T str) {
	for (int i = 0;i < n;i++)
	{
		if (a[i] == str) return (i + 1);
	}
	return -1;
}
/*词法分析*/
void analyse(FILE*fpin) {
	char ch = ' ';
	string arr = "";
	while ((ch = fgetc(fpin)) != EOF) {
		arr = "";
		if(IsFilter(ch)){}
		else if (IsLowLetter(ch)) {
			while (IsLowLetter(ch))
			{
				arr += ch;
				ch = fgetc(fpin);
			}
			if (IsKeyword(arr)) {
				printf("%3d  ", value(KEYWORD, 15, arr));
				cout<<arr<< "关键词：" << endl;
			}
			else {
				printf("%3d  ", IDENTIFIER);
				cout << arr << "标识符" << endl;
			}
		}
		else if (IsDigit(ch)) {
			while (IsDigit(ch) || (ch == '.'&&IsDigit(fgetc(fpin)))) {
				arr += ch;
				ch = fgetc(fpin);
			}
			fseek(fpin,-1L,SEEK_CUR);
			printf("%3d  ", CONSTANT);
			cout << arr << "整形数" << endl;
		}
		else if (IsUpLetter(ch) || IsLowLetter(ch) || ch == '_') {
			while (IsUpLetter(ch) || IsLowLetter(ch) || ch == '_' || IsDigit(ch)) {
				arr += ch;
				ch = fgetc(fpin);
			}
			fseek(fpin, -1L, SEEK_CUR);
			printf("%3d  ", CONSTANT);
			cout <<arr<<"标识符" << endl;
		}
		else switch (ch) {
		case '+':
		case '-':
		case '*':
		case '/':
		case '>':
		case '<':
		case '=':
		case '!': 
		{
			arr += ch;
			printf("%3d  ", value(OPERATOR, 8, *arr.data()));
			cout << arr << "运算符：" << endl;
			break;
		}
		case ';':
		case ',':
		case '(':
		case ')':
		case '[':
		case ']':
		case '{':
		case '}':
		{
			arr += ch;
			printf("%3d    ", value(SEPARATER, 8, *arr.data()));
			cout << arr << "  分隔符" << endl;
			break;
		}
		default:cout << "\"" << ch << "\":无法识别的字符！" << endl;
		}
	}
}
int main() {
	char inFile[40];
	FILE*fpin;
	cout << "请输入源文件名（包括路径和后缀）：";
	while (true) {
		cin >> inFile;
		if ((fpin = fopen(inFile, "r")) != NULL)
			break;
		else {
			cout << "文件名错误！" << endl;
			cout << "请输入原文件名（包括路径和后缀：）";
		}
	}
	cout << "-----词法分析如下-------" << endl;
	analyse(fpin);
	return 0;
}
#include<iostream>
#include<string>
#include<map>
#include<vector>
#include<stack>
#include<set>
#include<cstring>
using namespace std;
map<char, int>getnum;
char c[100];//��ö�Ӧ�ַ�
vector<string>proce;
int table[100][100];//Ԥ�������
int num = 0;int numvt = 0;
string first[100];
string follow[200];
void read() {
	memset(table,-1,sizeof(table));//��ʼ��
	getnum['#'] = 0;
	c[0] = '#';
	cout << "�������ս����" << endl;
	char x;
	do {
		cin >> x;
		getnum[x] = ++num;
		c[num] = x;
	} while (cin.peek() != '\n');
	numvt = ++num;
	getnum['@'] = numvt;//kong zi
	c[num] = ('@');
	cout << "��������ս������" << endl;
	do {
		cin >> x;
		getnum[x] = ++num;
		c[num] = x;
	} while (cin.peek() != '\n');
	cout << "���������в���ʽ��������@��ʾ������end������" << endl;
	string pro;
	while (cin >> pro && pro != "end") {
		string ss;
		ss += pro[0];
		for (unsigned int i = 3;i < pro.size();i++) {
			if (pro[i] == '|') {
				proce.push_back(ss);
				ss.clear();
				ss += pro[0];
			}
			else {
				ss += pro[i];
			}
		}
		proce.push_back(ss);
	}
}
void jiao(string &a, string b) {//ȡa��b�Ľ���������ֵ��a
	set<char>se;
	for (unsigned int i = 0;i < a.size();i++) {
		se.insert(a[i]);
	}
	for (unsigned int i = 0;i < b.size();i++) {
		se.insert(b[i]);
	}
	string ans;
	set<char>::iterator it;
	for (it = se.begin();it != se.end();it++)
		ans += *it;
	a = ans;
}
string get_f(int vn, int &has_0) {
	if (vn == numvt) has_0 = 1;
	if (vn < numvt) return first[vn];
	string ans;
	for (unsigned int i = 0;i < proce.size();i++) {
		if (getnum[proce[i][0]] == vn)
		ans += get_f(getnum[proce[i][1]], has_0);
	}
	return ans;
}
void getfirst() {
	for (int i = 1;i <= numvt;i++) {//�ս����first�����䱾��
		first[i] += ('0' + i);
	}
	for (unsigned int j = 0;j< proce.size();j++) {//ɨ�����в���ʽ
		int k = 0;int has_0 = 0;//k ɨ��ò���ʽ
		do {
			has_0 = 0;
			k++;
			if (k == proce[j].size()) {//�Ƶ����һ�����򸽼ӿ���
				first[getnum[proce[j][0]]] += ('0' + numvt);
				break;
			}
			jiao(first[getnum[proce[j][0]]], get_f(getnum[proce[j][k]], has_0));//�ϲ�
		} while (has_0);//ֱ���޷��Ƴ�����Ϊֹ
	}
}
void print_first() {
	cout << "first�����£�" << endl;
	for (int i = 1;i <= num;i++) {
		cout << "first[" << c[i] << "]:";
		for (unsigned int j = 0;i < first[i].size();j++){
			cout << c[first[i][j] - '0'] << "";
			}
			cout << endl;
	}
	cout << endl;
}
void getfollow() {
	jiao(follow[getnum[proce[0][0]]], "0");//����ӡ�#��
	for (unsigned int j = 0;j< proce.size();j++) {//ɨ�����ʽ
		for (unsigned int jj = 1;jj < proce[j].size();jj++) {//ÿ�����ս����follow��
			if (getnum[proce[j][jj]] <= numvt)continue;//vt��follow��
			int k = jj;int has_0;
			do
			{
				has_0 = 0;
				k++;
				if (k == proce[j].size()) {//�����Ƴ����֣�follow�����ڲ���ʽ��ߵ�vn
					jiao(follow[getnum[proce[j][jj]]], follow[getnum[proce[j][0]]]);
					break;
				}
				jiao(follow[getnum[proce[j][jj]]], get_f(getnum[proce[j][k]], has_0));
			} while (has_0);
		}
	}
}
void gettable() {//�õ�Ԥ�������
	for (unsigned int i = 0;i < proce.size();i++) {
		if (proce[i][1] == '@') {
			string flw = follow[getnum[proce[i][0]]];
			for (unsigned int k = 0;k < flw.size();k++) {
				table[getnum[proce[i][0]]][flw[k] - '0'] = i;
			}
		}
		string temps = first[getnum[proce[i][1]]];
		for (unsigned int j = 0;j < temps.size();j++) {
			if (temps[j] != ('0' + numvt)) {
				table[getnum[proce[i][0]]][temps[j] - '0'] = i;
			}
			else {
				string flw = follow[getnum[proce[i][1]]];
				for (unsigned int k = 0;k < flw.size();k++) {
				table[getnum[proce[i][0]]][flw[k] - '0'] = i;
				}
			}
		}
	}
}
string get_proce(int i) {//�ɶ�Ӧ�±��ò���ʽ
	if (i < 0)return "";
	string ans;
	ans += proce[i][0];
	ans += "->";
	for (unsigned int j = 1;j < proce[i].size();j++) {
		ans += proce[i][j];
	}
	return ans;
}
void print_table() {
	cout << "Ԥ����������£�" << endl;
	for (int i = 0;i < numvt;i++) {
		cout << '\t' << c[i];
	}
	cout << endl;
	for (int i = numvt + 1;i <= num;i++) {
		cout << c[i];
		for (int j = 0;j < numvt;j++) {
			cout << '\t' << get_proce(table[i][j]);
		}
		cout << endl;
	}
	cout << endl;
}
void print_follow() {
	cout << "follow�����£�" << endl;
	for (int i = numvt + 1;i <= num;i++) {
		cout << "follow[" << c[i] << "]:";
		for (unsigned int j = 0;j < follow[i].size();j++) {
			cout << c[follow[i][j] - '0'] << "";
		}
		cout << endl;
	}
	cout << endl;
}
string word;
bool analyze() {//�ܿأ�����word�ĺϷ��ԣ����Ϸ���������в���ʽ
	stack<char>sta;
	sta.push('#');
	sta.push(proce[0][0]);
	int i = 0;
	while (!sta.empty()) {
		int cur = sta.top();
		sta.pop();
		if (cur == word[i]) {
			i++;
		}
		else if (cur == '#') {
			return 1;
		}
		else if (table[getnum[cur]][getnum[word[i]]] != -1) {
			int k = table[getnum[cur]][getnum[word[i]]];
			cout << proce[k][0] << "->";
			for (unsigned int j = 1;j < proce[k].size();j++) {
				cout << proce[k][j];
			}
			cout << endl;
			for (int j = proce[k].size() - 1;j > 0;j--) {
				if (proce[k][j] != '@') {
					sta.push(proce[k][j]);
				}
			}
		}
		else {
			return 0;
		}
	}
	return 1;
}
/*
int main() {
	read();
	getfirst();
	getfollow();
	getfollow();
	gettable();
	print_first();
	print_follow();
	print_table();
	cout << "�������֣�" << endl;
	cin >> word;
	if (analyze()) {
		cout << "succeed!������Ч�����в���ʽ���ϡ�" << endl;
	}
	else {
		cout << "error!" << endl;
	}
	return 0;
}*/
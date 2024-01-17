#include<bits/stdc++.h>
using namespace std;

namespace Hash { // 进制哈希
#define hashCode unsigned long long
	const int p = 13131;
	hashCode getHash(const string& str) {
		hashCode ans = 0;
		int len = str.length();
		for(int i = 0; i < len; ++ i) {
			ans = ans * p + str[i];
		}
		return ans;
	}
}

namespace Trie { // 字典树
	const int N = 1000005;
	const int CharSet = 65;

	int trie[N][CharSet + 2];
	int data[N];
	bool exsit[N];
	int cur;

	int T(char ch) {
		if(ch >= '0' && ch <= '9') return ch - '0';
		if(ch >= 'a' && ch <= 'z') return ch - 'a' + 10;
		if(ch >= 'A' && ch <= 'Z') return ch - 'A' + 10 + 26;
	}

	void insert(const string& str,int value) {
		int p = 0;
		int len = str.length();

		for(int i = 0; i < len; ++ i) {
			char ch = T(str[i]);
			if(!trie[p][ch]) trie[p][ch] = ++ cur;
			p = trie[p][ch];
		}

		exsit[p] = true;
		data[p] = value;
	}

	int query(const string& str) {
		int p = 0;
		int len = str.length();

		for(int i = 0; i < len; ++ i) {
			char ch = T(str[i]);
			if(!trie[p][ch]) return -1;
			p = trie[p][ch];
		}

		if(!exsit[p]) return -1;
		return data[p];
	}
}

namespace KMP { // KMP
	const int N = 100005;
	int next[N];
	vector<int> patterns;

	void buildNext(const string& p) { // 最长前后缀可能有重叠部分
		int len = p.length();
		next[0] = next[1] = 0;

		for(int i = 1; i < len; ++ i) {
			int j = next[i];
			while(j && p[i] != p[j]) j = next[j];
			if(p[i] == p[j]) next[i + 1] = j + 1;
			else next[i + 1] = 0;
		}
	}

	void buildNext_ignoreRepeat(const string& p) { // 最长前后缀无重叠部分
		int len = p.length();
		next[0] = next[1] = 0;

		for(int i = 1; i < len; ++ i) {
			int j = next[i];
			while(j && p[i] != p[j]) j = next[j];
			if(p[i] == p[j]) next[i + 1] = j + 1;
			else next[i + 1] = 0;
			if((next[i + 1] << 1) > i + 1) {
				int j = next[i + 1];
				while(j && (next[j] << 1) > i + 1) j = next[j];
				next[i + 1] = next[j];
			}
		}
	}

	vector<int>& kmp(const string& str,const string& p) {
		buildNext(p);
		patterns.clear();
		int j = 0;
		int lens = str.length(),lenp = p.length();

		for(int i = 0; i < lens; ++ i) {
			while(j && str[i] != p[j]) j = next[j];
			if(str[i] == p[j]) j ++;
			if(j == lenp) patterns.push_back(i - lenp + 1);
		}
		return patterns;
	}

	int* getNextArray() {
		return next;
	}
}

namespace AC { // AC自动机
	using namespace Trie;

	int fail[N];

	void buildFail() {
		queue<int> q;

		for(int i = 0; i < CharSet; ++ i) {
			if(trie[0][i]) q.push(trie[0][i]);
		}

		while(!q.empty()) {
			int fa = q.front();
			q.pop();

			for(int i = 0; i < CharSet; ++ i) {
				if(trie[fa][i]) {
					fail[trie[fa][i]] = trie[fail[fa]][i];
					q.push(trie[fa][i]);
				} else trie[fa][i] = trie[fail[fa]][i];
			}
		}
	}

	int query(const string& str) {
		int p = 0;
		int ans = 0;
		int len = str.length();

		for(int i = 0; i < len; ++ i) {
			int ch = T(str[i]);
			p = trie[p][ch];
			int temp = p;

			while(temp && exsit[temp] != -1) {
				ans += exsit[temp];
				exsit[temp] = -1;
				temp = fail[temp];
			}
		}
		return ans;
	}
}

namespace Manacher { // Manacher
	const int N = 110000005;
	int P[N];

	string change(const string& str) {
		int len = str.length();

		string ans = "@|";

		for(int i = 0; i < len; ++ i) {
			ans += str[i];
			ans += '|';
		}

		ans += '!';
		return ans;
	}

	int query(const string& base) {
		string str = change(base);
		int len = str.length();
		int R = 0;
		int C = 0;
		int ans = 0;
		memset(P,0,sizeof(P));

		for(int i = 0; i < len; ++ i) {
			if(i > R) P[i] = 1;
			else P[i] = min(P[(C << 1) - i],R - i);

			while(str[i - P[i]] == str[i + P[i]]) P[i] ++;
			if(P[i] + i > R) {
				R = P[i] + i;
				C = i;
			}

			ans = max(ans,P[i]);
		}

		return ans - 1;
	}
}

namespace SA { // SA 后缀数组
	const int N = 1000005;
	int sa[N << 1],rk[N << 1],temp[N << 1];

	const int* buildSA(const string& str) {
		int len = str.length();

		for(int i = 1; i <= len; ++ i) {
			sa[i] = i;
			rk[i] = str[i - 1];
		}

		for(int w = 1; w <= len; w <<= 1) {
			sort(sa + 1,sa + len + 1,[w](int x,int y) ->bool const {
				if(rk[x] == rk[y]) return rk[x + w] < rk[y + w];
				return rk[x] < rk[y];
			});
			memcpy(temp,rk,sizeof(rk));
			for(int i = 1,p = 0; i <= len; ++ i) {
				if(temp[sa[i]] == temp[sa[i - 1]] && temp[sa[i] + w] == temp[sa[i - 1] + w]) rk[sa[i]] = p;
				else rk[sa[i]] = ++ p;
			}
		}
		return sa;
	}
}

namespace Set { //并查集
	const int N = 100005;
	int f[N],r[N];

	void init(int n) {
		for(int i = 1; i <= n; ++ i) {
			f[i] = i;
			r[i] = 1;
		}
	}

	int find(int w) {
		if(f[w] == w) return w;
		return f[w] = find(f[w]);
	}

	void merge(int a,int b) {
		int x = find(a),y = find(b);
		if(r[x] > r[y]) swap(x,y);
		r[y] += r[x];
		f[x] = y;
	}

	bool isSame(int x,int y) {
		return find(x) == find(y);
	}
}

namespace SegTree { //线段树
#define l(p) t[(p)].l
#define r(p) t[(p)].r
#define add(p) t[(p)].add
#define sum(p) t[(p)].sum
#define lc(p) ((p) << 1)
#define rc(p) ((p) << 1 | 1)
#define len(p) (r(p) - l(p) + 1)
	const int N = 1000005;
	struct node {
		int l;
		int r;
		int sum;
		int add;
	} t[N];

	void push_up(int p) {
		sum(p) = sum(lc(p)) + sum(rc(p));
	}

	void push_down(int p) {
		if(add(p)) {
			sum(lc(p)) += add(p) * len(lc(p));
			sum(rc(p)) += add(p) * len(rc(p));
			add(lc(p)) += add(p);
			add(rc(p)) += add(p);
			add(p) = 0;
		}
	}

	void build(int p,int l,int r,int arr[]) {
		l(p) = l;
		r(p) = r;
		if(l == r) {
			sum(p) = arr[l];
			return;
		}
		int mid = (l + r) >> 1;
		build(lc(p),l,mid,arr);
		build(rc(p),mid + 1,r,arr);
		push_up(p);
	}

	void change(int p,int x,int v) {
		if(l(p) == r(p)) {
			sum(p) = v;
			return;
		}
		push_down(p);
		int mid = (lc(p) + rc(p)) >> 1;
		if(x <= mid) change(lc(p),x,v);
		else change(rc(p),x,v);
		push_up(p);
	}

	void increase(int p,int x,int v) {
		if(l(p) == r(p)) {
			sum(p) += v;
			return;
		}
		push_down(p);
		int mid = (lc(p) + rc(p)) >> 1;
		if(x <= mid) increase(lc(p),x,v);
		else increase(rc(p),x,v);
		push_up(p);
	}

	void increase(int p,int l,int r,int v) {
		if(l <= l(p) && r >= r(p)) {
			sum(p) += len(p) * v;
			add(p) += v;
			return;
		}
		push_down(p);
		int mid = (l(p) + r(p)) >> 1;
		if(l <= mid) increase(lc(p),l,r,v);
		if(r > mid) increase(rc(p),l,r,v);
		push_up(p);
	}

	int query(int p,int x) {
		if(l(p) == r(p)) return sum(p);
		push_down(p);
		int mid = (l(p) + r(p)) >> 1;
		if(x <= mid) return query(lc(p),x);
		return query(rc(p),x);
	}

	int query(int p,int l,int r) {
		if(l <= l(p) && r >= r(p)) return sum(p);
		push_down(p);
		int mid = (l(p) + r(p)) >> 1;
		int ans = 0;
		if(l <= mid) ans += query(lc(p),l,r);
		if(r > mid) ans += query(rc(p),l,r);
		return ans;
	}
}

namespace Graph {
	const int N = 1005;
	struct edge {
		int v;
		int w;
		int next;
	} e[N];
	int head[N];
	int cur = 0;

	void addEdge(int u,int v,int w) {
		e[++ cur].v = v;
		e[cur].w = w;
		e[cur].next = head[u];
		head[u] = cur;
	}
}

namespace Tarjan {
	using namespace Graph;
	int dfn[N],low[N];
	int tot = 0;
	int sccid[N],s[N];
	int top = 0;
	int cnt = 0;
	void SCC(int u) {
		low[u] = dfn[u] = ++ tot;
		s[++ top] = u;
		for(int i = head[u]; i; i = e[i].next) {
			int v = e[i].v;
			if(!dfn[v]) {
				SCC(v);
				low[u] = min(low[u],low[v]);
			} else if(!sccid[v]) {
				low[u] = min(low[u],dfn[v]);
			}
		}
		if(low[u] == dfn[u]) {
			cnt ++;
			int x;
			do {
				x = s[top --];
				sccid[x] = cnt;
			} while(u != x);
		}
	}

	bool SameSCC(int u,int v) {
		return sccid[u] == sccid[v];
	}
}

int main() {

	return 0;
}


/*

#include<bits/stdc++.h>
using namespace std;

const int mod = 1000000007;

namespace KMP{
	const int N = 1000005;
	int next[N];
	int num[N];
	int jumpCount[N];

	void getNext(const string& p){
		next[0] = next[1] = 0;
		int len = p.length();

		for(int i = 1;i < len;++ i){
			int j = next[i];
			while(j && p[i] != p[j]) j = next[j];
			if(p[i] == p[j]) next[i + 1] = j + 1;
			else next[i + 1] = 0;
		}
	}

	void getJumpCount(int length){
		for(int i = 1;i <= length;++ i){
			jumpCount[i] = 0;
			int j = next[i];
			cout<<j<<">";
			while(j){
				if(jumpCount[j]){
					jumpCount[i] += jumpCount[j];
					break;
				}
				j = next[j];
//				cout<<j<<">";
				jumpCount[i] ++;
			}
//			cout<<"\n";
		}
	}

	void getNum(int length){
		for(int i = 1;i <= length;++ i){
			num[i] = 0;
			int j = next[i];
			while(j && (j << 1) > i) j = next[j];
			while(j){
				if(jumpCount[j]){
					num[i] += jumpCount[j];
					break;
				}
				j = next[j];
				num[i] ++;
			}
		}
	}
}

int main() {
	ios::sync_with_stdio(false);
	cin.tie(0);
	cout.tie(0);
	int T;
	cin>>T;
	while(T --){
		string str;
		cin>>str;
		KMP::getNext(str);
		KMP::getJumpCount(str.length());
		KMP::getNum(str.length());
		long long ans = 1;
		for(int i = 1;i <= str.length();++ i){
			cout<<str[i - 1]<<' '<<KMP::jumpCount[i]<<endl;
			ans = ans * (KMP::num[i] + 1) % mod;
		}
		cout<<ans<<"\n";
	}
	return 0;
}


5
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaxpuvf
abababababababababababababababababababababababdgcd
abcbaabcbaabcbaabcbaabcbaabcbaabcbaabcbaabcbafmlqh
abacababacababacababacababacababacababacababadjyxq
aabaacaabaacaabaacaabaacaabaacaabaacaabaacaabjtaxw


592345761
371390093
121623872
675691877
481106999


*/

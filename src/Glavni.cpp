#include <iostream>
#include <fstream>
#include <string>
#include <regex>
#include <list>
#include <sstream>
#include <iomanip>
#include <bitset>
#include <cmath>

using namespace std;

class Sekcija {
public:
	int offset;
	int sadrzaj;
	string sadrzina;
	string sekc = "";
	string tip = "";
	Sekcija(int o, int s) {
		offset = o;
		sadrzaj = s;
		sadrzina = "";
	}
	Sekcija() {
		offset = sadrzaj = 0;
		sadrzina = "";
	}
};

class rel_zapis {
public:
	int offset;
	string tip;
	int rb;
	rel_zapis(int o, string t, int r) {
		offset = o;
		tip = t;
		rb = r;
		
	}
	rel_zapis() {
		offset = rb = 0;
		tip = "";
	}
};

class Elf_Symbol {
public:
	string name;
	int value;
	int size;
	char binding;
	int rb;
	char type;
	string section;
	Elf_Symbol(string n, int v, int s, char b, string sec, char t) {
		name = n;
		value = v;
		size = s;
		binding = b;
		section = sec;
		type = t;
		
	}
	Elf_Symbol() {//za jednu upotrebu u obradi_instrukciju
		value = size = rb = 0;
		binding = 'g';
		type = 'd';
		section = "UND";
		name = "";
	}
};
//potrebni globalni podaci
int flag1 = 0;
int lc2 = 0;
int prva_sekcija = 1;
unsigned lc = 0;
int br_sekcija = 0;
int rb_sekcije = 1;
int rb_simbola = 0;
int indikator = 0;
int ind_instrukcija = 1;
int vel_instr2 = 0;//indikator velicine instrukcije
int ind_ret = 0;
int broj_linije = 0;
int broj_simbola_u_labeli = 0;
int pocetna_adresa = 0;
vector<int>za_skip;
vector<int>za_align;

string s, tekuca_sekcija;
list<Elf_Symbol*> tabela_simbola;
list<Elf_Symbol*>::iterator it;
list<rel_zapis*> rel_text;
list<rel_zapis*>::iterator it_rel;
list<rel_zapis*> rel_data;
list<rel_zapis*> rel_rodata;
list<Sekcija*> tabela_text;
list<Sekcija*> tabela_data;
list<Sekcija*> tabela_rodata;
list<Sekcija*> tabela_bss;
list<Sekcija*>::iterator iter;
stringstream ss;
std::smatch match;
ofstream logg;

//regexi za direktive
regex ch(".char\\s+"); regex global(".global\\s+"); regex skip(".skip\\s+"); regex lo(".long\\s+"); regex ali(".align\\s+");
regex word(".word\\s+");

//regexi za instrukcije
regex add("add"); regex sub("sub"); regex mul("mul"); regex divv("div"); regex cmp("cmp");
regex andd ("and"); regex orr("or"); regex nott("not"); regex tst("test"); regex psh("push");
regex popp("pop"); regex call("call"); regex iret("iret"); regex mov("mov"); regex shl("shl"); regex shr("shr");
regex jmp("jmp"); regex ret("ret");
//uslovni regexi
regex eq("eq"); regex ne("ne"); regex gt("gt"); regex al("al");
//regexi operanada
regex regpomlab1("r[0-7]\\[[a-z]+\\],\\s*r[0-7]"); 
regex regpomlab2("r[0-7],\\s*r[0-7]\\[[a-z]+\\]");
regex regpombr1("r[0-7]\\[\\d+\\],\\s*r[0-7]");
regex regpombr2("r[0-7],\\s*r[0-7]\\[\\d+\\]");
regex pcrel1("\\$[a-z]+,\\s*r[0-7]");
regex immed2("r[0-7],\\s*-?[0-9]+");
regex immed1("-?[0-9]+,\\s*r[0-7]");
regex pcrel2("r[0-7],\\s*\\$[a-z]+");
regex memdir1("[a-z]+,\\s*r[0-7]");
regex memdir2("r[0-7],\\s*[a-z]+");
regex memind1("\\*\\d+,\\s*r[0-7]");//* adresa sa adrese, memorijsko indirektno
regex memind2("r[0-7],\\s*\\*\\d+");
regex const1("&[a-z]+,\\s*r[0-7]");//za citanje direktno labele
regex const2("r[0-7],\\s*&[a-z]+");
regex regdir1("r[0-7],\\s*r[0-7]");
//regexi za instrukcije koje mogu biti samo 2B
regex regpomlab("r[0-7]\\[[a-z]+\\]");
regex regpombr("r[0-7]\\[\\d+\\]");
regex pcrel("\\$[a-z]+");
regex immed("-?[0-9]+");
regex memdir("[a-z]+");
regex memind("\\*\\d+");
regex constt("&[a-z]+");
regex regdir("r[0-7]");
regex psw("psw");
//prazan string ili sa nevalidnim simbolima
regex prazan("\\s+");

//provjere za jump
regex prov1("jmp[a-z]*\\s+\\$[a-z]+");
regex prov2("jmp[a-z]*\\s+[a-z]+");

void pretraga_na_instrukciju(string s) {//za prvi prolaz
	lc += 2;

	if (regex_search(s, ret) || regex_search(s, iret))return;
	if (regex_search(s, jmp) && !(regex_search(s, prov1) || regex_search(s, prov2))) {
		logg.open("log.txt", std::ofstream::out | std::ofstream::app);
		logg << "Greska u adresiranju, jump moze imati samo pcrel ili memdir adresiranje. Broj linije: " << broj_linije << endl;
		logg.close();
		cout << "Doslo je do greske. Greska se nalazi u log.txt\n";
		exit(1);
	}


	if (regex_search(s, regdir1)) {
		if (!(regex_search(s, regpombr1) || regex_search(s, regpombr2) || regex_search(s, pcrel1) || regex_search(s, immed2) || regex_search(s, pcrel2) || regex_search(s, memdir1)
			|| regex_search(s, memind1) || regex_search(s, memind2) || regex_search(s, const1) || regex_search(s, const2)
			|| regex_search(s, regpomlab1) || regex_search(s, regpomlab2) || regex_search(s, call) || regex_search(s, jmp)))return;
	
	}

	if (regex_search(s, regpombr1) || regex_search(s, regpombr2) || regex_search(s, pcrel1) || regex_search(s, immed2) || regex_search(s, pcrel2) || regex_search(s, memdir1)
			|| regex_search(s, memdir2) || regex_search(s, memind1) || regex_search(s, memind2) || regex_search(s, const1) || regex_search(s, const2)
			||regex_search(s,regpomlab1) || regex_search(s, regpomlab2)||regex_search(s,call)||regex_search(s,jmp)) {
			lc += 2;
			return;
	}


	else if (regex_search(s, immed1)&&(!(regex_search(s,psh)))) {
		logg.open("log.txt", std::ofstream::out | std::ofstream::app);
		logg << "Greska u adresiranju, neposredna vrijednost kao prvi operand ili 2 operanda zahtijevaju po dodatni bajt na liniji: " << broj_linije << endl;
		logg.close();
		cout << "Doslo je do greske. Greska se nalazi u log.txt\n";
		exit(1);
	}

	else if (!((regex_search(s, psh) || regex_search(s, popp)) && regex_search(s, regdir))) {
		lc += 2;
		return;
	}

	else if (!(regex_search(s, psh) || regex_search(s, popp) || regex_search(s, call) || regex_search(s, jmp) || regex_search(s, iret) || regex_search(s, ret))) {
		logg.open("log.txt", std::ofstream::out | std::ofstream::app);
		logg << "Greska u adresiranju, neposredna vrijednost kao prvi operand ili 2 operanda zahtijevaju po dodatni bajt na liniji: " << broj_linije << endl;
		logg.close();
		cout << "Doslo je do greske. Greska se nalazi u log.txt\n";
		exit(1);//ako nema poklapanja sa gornjim adresiranjima, a nije jedna od instrukcija koje imaju samo 1 operand, onda je greska u instrukciji
	}
}

void pretraga_na_direktivu(string s) {
	if (regex_search(s, ch)) {
		regex_replace(s, ch, "");
		lc++;
		broj_simbola_u_labeli++;
		for (int i = 0; i < s.length(); i++) {
			if(s[i]==','){
				lc++; 
				broj_simbola_u_labeli++;
			}
		}
		indikator = 0;//char
		ind_instrukcija = 0;
	}
	else if (regex_search(s, lo)) {
		regex_replace(s, lo, "");
		lc += 4;
		broj_simbola_u_labeli++;
		for (int i = 0; i < s.length(); i++) {
			if (s[i] == ',') {
				lc+=4;
				broj_simbola_u_labeli++;
			}
		}
		indikator = 1;//long
		ind_instrukcija = 0;
	}
	else if (regex_search(s, word)) {
		regex_replace(s, word, "");
		lc += 2;
		broj_simbola_u_labeli++;
		for (int i = 0; i < s.length(); i++) {
			if (s[i] == ',') {
				lc += 2;
				broj_simbola_u_labeli++;
			}
		}
		indikator = 2;//word
		ind_instrukcija = 0;
	}
	else if (regex_search(s, skip)) {
		s = regex_replace(s, skip, "");
		string f = "";
		for (int i = 0; i < s.length(); i++) {
			for(int j=i;j<s.length();j++,i++)
				if(isdigit(s[j]))f += s[j];
				else if ((s[j] == ',') || (s[j] == ' ') || (s[j] == '\t'))break;

			if (!f.empty()){
			int broj = stoi(f);
			f = "";
			za_skip.push_back(broj);
			lc += broj; 
			}
			
		}
		indikator = 3;//skip
		ind_instrukcija = 0;
	}
	else if (regex_search(s, ali)) {
		s = regex_replace(s, ali, "");
		string f = "";
		int z = 0;
		for (int i = 0; i < s.length(); i++) {
			for (int j = i; j < s.length(); j++,i++)
				if (isdigit(s[j]))f += s[j];
				else if ((s[j] == ',')||(s[j]==' ')||(s[j] == '\t'))break;
			if (!f.empty()) {
				int broj = stoi(f);
				f = "";
				broj = pow(2, broj);
				while (lc%broj != 0) {
					lc++;
					z++;
				}
				if(z)za_align.push_back(z);
				z = 0;
			}
		}
		indikator = 4;//align
		ind_instrukcija = 0;

	}
}

int logicalShiftR(int x, int n) {
	return x >> n & (1 << sizeof(int) - n) - 1;
}//pomocna funkcija za little endian konverziju

string formatiraj_hex(string l) {
	string str="";
	for (int i = 0; i < l.length(); i++) {
		str += l[i];
		if (i % 2 != 0)str += " ";
	}
	return str;
}

void obradi_labelu(string s, Sekcija *r,int l, int vel) {
	string f = "";
	vector<string> simboli_text;
	vector<string> simboli_data;
	vector<string> simboli_rodata;
	vector<string> simboli_bss;
	vector<string>::iterator brojac;
	vector<int>::iterator brojac_int;
	int prvi = 1;
	int z = 0;
	int indikator_text=0;//sluzi za neke provjere kasnije
	int indikator_data=0;
	int indikator_rodata=0;
	int indikator_bss=0;
	string operacije = "";
	int redni_broj=0;
	int oznaka = 0;
	list<Elf_Symbol*>::iterator it;
	list<Elf_Symbol*>::iterator iter;
	int j = 0;

	if (regex_search(s, skip)) {
		r->sadrzaj = 0;
		r->sekc = tekuca_sekcija;
		for(brojac_int=za_skip.begin();brojac_int!=za_skip.end();brojac_int++) {
			for(int i=0;i<*brojac_int;i++)r->sadrzina += "00";
		}
		r->sadrzina = formatiraj_hex(r->sadrzina);
		if (r->sekc == "text")tabela_text.push_back(r);
		else if (r->sekc == "data")tabela_data.push_back(r);
		else if (r->sekc == "rodata")tabela_rodata.push_back(r);
		za_skip.clear();
		return;
	}

	if (regex_search(s, ali)) {
		int pomjeraj = 0;
		r->sadrzaj = 0;
		r->sekc = tekuca_sekcija;
		for (brojac_int = za_align.begin(); brojac_int != za_align.end();brojac_int++) {
			for (int i = 0; i < *brojac_int; i++) {
				r->sadrzina += "00"; pomjeraj++;
			}
			if (pomjeraj != 0) {
				r->sadrzina = formatiraj_hex(r->sadrzina);
				if (r->sekc == "text")tabela_text.push_back(r);
				else if (r->sekc == "data")tabela_data.push_back(r);
				else if (r->sekc == "rodata")tabela_rodata.push_back(r);
				pomjeraj = 0;
				r = new Sekcija();
			}

		}
		za_align.clear();
		return;
	}

	while (j < s.length()) {
		for (int i = j; i < s.length(); i++) {//izdvajanje slova iz labela
			j++;
			if (s[0] != '-') {//ako je poslat samo jedan broj u funkciju i ako je negativan, ova provjera je potrebna kako bi se on korektno zapisao
				if (s[i] != '+'&&s[i] != '-')f += s[i];
				else {
					operacije += s[i];
					break;
				}
			}
			else f += s[i];
			
		}
		int lokalni = 1;
		for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) 
			if (!(*it)->name.compare(f)) { oznaka = 1; 
				if ((*it)->binding == 'g')lokalni = 0;
				break;
					}
			if (oznaka) {
				
				if (prvi == 0) {
					z++;//uradjeno ovako zato sto operacije dobiju novu operaciju prije nego sto obrade staru i da se z povecava u prethodnoj petlji
					if (operacije[z - 1] == '+') {//sada bismo obradjivali operaciju koja slijedi iza odgovarajuce u nizu, koja se odnosi na sledeci operand
						if(lokalni) r->sadrzaj += (*it)->value;//ako je lokalni simbol saberi trenutnu vrijednost, ako je globalni nemoj sabirat posto se upisuje adresa globalnog simbola u
						//relokacioni zapis, a ne samo adresa sekcije
						if (!(*it)->section.compare("text")) { indikator_text++; simboli_text.push_back(f); }
						else if (!(*it)->section.compare("data")) { indikator_data++; simboli_data.push_back(f); }
						else if (!(*it)->section.compare("rodata")) { indikator_rodata++; simboli_rodata.push_back(f); }
						else { indikator_bss++; simboli_bss.push_back(f); }

						//ovi indikatori se povecavaju kada se sabiraju simboli iz iste sekcije, a smanjuju kada se ti simboli oduzimaju
						//kasnije ce ovo sluziti na sledeci nacin: ako je indikator 0, ne treba generisati relokacione zapise, posto to znaci da se jednak broj simbola
					}//iz iste sekcije sabrao i oduzeo, pa ce vrijednost biti konstantna; ako je indikator razlicit od nule, to znaci da je toliko simbola iz te sekcije bilo sabrano/oduzeto 
					else {
						
					if (lokalni) r->sadrzaj -= (*it)->value; //u zavisnosti od toga je li >0 ili <0 znaci da treba generisati toliko relokacionih zapisa jer su se sabirale adrese koje generise linker kasnije
					if (!(*it)->section.compare("text")) { indikator_text--; simboli_text.push_back(f); }
					else if (!(*it)->section.compare("data")) { indikator_data--; simboli_data.push_back(f); }
					else if (!(*it)->section.compare("rodata")) { indikator_rodata--; simboli_rodata.push_back(f); }
					else { indikator_bss--; simboli_bss.push_back(f); }
					}
				}
				else {

					if (lokalni) r->sadrzaj += (*it)->value; prvi = 0;
					if (!(*it)->section.compare("text")) { indikator_text++; simboli_text.push_back(f); }
					else if (!(*it)->section.compare("data")) { indikator_data++; simboli_data.push_back(f); }
					else if (!(*it)->section.compare("rodata")) { indikator_rodata++; simboli_rodata.push_back(f); }
					else { indikator_bss++; simboli_bss.push_back(f); }
				}
				

			}
			else {
				int broj = 0;
				int indik = 1;
				try { 
					broj = stoi(f); 
				}
				catch (exception e) {//ako ne moze da konvertuje string u int, a prije toga nije nasao u tabeli simbola odgovarajuci simbol, to znaci da se u labeli nalazi neki nedefinisani simbol
					indik = 0;//dodajemo ga u tabelu simbola kao globalni simbol i u relokacioni zapis
					Elf_Symbol *simbol = new Elf_Symbol(f, -1, 0, 'g', "UND", '?');//indikator=0 oznacava da nije pronadjen simbol, sto znaci da simbol koji dodajemo je globalni
					tabela_simbola.push_back(simbol);//sto dalje znaci da njegovu vrijednost ne treba dodati na postojecu vrijednost u zapisu za sekciju, jer se njegova adresa(vrijednost)direktno upisuje
					simbol->rb = tabela_simbola.size()+1;
					rel_zapis* zap = new rel_zapis(l, "R_386_16", simbol->rb);
					if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);//stavi relokacioni zapis u odgovarajucu listu relokacionih zapisa (za tekucu sekciju)
					else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
					else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
						
					
				}
				if (indik) {
					z++;
					if (prvi == 0) {
						if (operacije[z - 1] == '+')//na osnovu operacije saberi ili oduzmi
							r->sadrzaj += broj;
						else r->sadrzaj -= broj;
					}
					else {
						r->sadrzaj += broj;
						prvi = 0;
					}
				}
			}
			oznaka = 0;
		f = "";
	}

	if (indikator_data != 0) {
		indikator_data = abs(indikator_data);
		simboli_data.erase(simboli_data.begin(), simboli_data.begin() + (simboli_data.size() - indikator_data));//uklanjanje prvih par simbola koji ne prave suficit/deficit, znaci ako je
		for (brojac = simboli_data.begin(); brojac < simboli_data.end(); brojac++) {//bilo 4 simbola od kojih se 2 sabiraju i 2 oduzimaju i jos na to 2 koja se sabiraju, znaci prva 4 za koje ne
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {//trebaju relokacije ce biti ignorisani, posto je njihova razlika konstantna, a ova dvo ste sabiraju trebaju im
				if (!(*it)->name.compare(*brojac)) {//relokacioni zapisi jer zavise vrijednosti od adrese
					if ((*it)->binding == 'g') {//ako je globalni simbol uzmi njegov redni broj i upisi ga u relokacioni zapis, u suprotnom pronadji redni broj labele i upisi ga 
						rel_zapis* zap = new rel_zapis(l,"R_386_16",(*it)->rb);
						if(!tekuca_sekcija.compare("data"))rel_data.push_back(zap);//stavi relokacioni zapis u odgovarajucu listu relokacionih zapisa (za tekucu sekciju)
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					else {
						for (iter = tabela_simbola.begin(); iter != tabela_simbola.end(); iter++)
							if (!(*iter)->name.compare("." + (*it)->section))break;
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*iter)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					break;
				}
			}
		}
	}

	if (indikator_text != 0) {
		indikator_text = abs(indikator_text);
		simboli_text.erase(simboli_text.begin(), simboli_text.begin() + (simboli_text.size()-indikator_text));//uklanjanje prvih par simbola, i pravljenje relokacionih zapisa za preostale
		for (brojac = simboli_text.begin(); brojac < simboli_text.end(); brojac++) {// za svaki element u vektoru treba pronaci element iz tabele simbola
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
				if (!(*it)->name.compare(*brojac)) {
					if ((*it)->binding == 'g') {
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*it)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					else {
						for (iter = tabela_simbola.begin(); iter != tabela_simbola.end(); iter++)
							if (!(*iter)->name.compare("." + (*it)->section))break;
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*iter)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					break;
				}
			}
		}
	}

	if (indikator_rodata != 0) {
		indikator_rodata = abs(indikator_rodata);
		simboli_rodata.erase(simboli_rodata.begin(), simboli_rodata.begin() + (simboli_rodata.size() - indikator_rodata));//uklanjanje prvih par simbola, i pravljenje relokacionih zapisa za preostale
		for (brojac = simboli_rodata.begin(); brojac < simboli_rodata.end(); brojac++) {// za svaki element u vektoru treba pronaci element iz tabele simbola
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
				if (!(*it)->name.compare(*brojac)) {
					if ((*it)->binding == 'g') {
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*it)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					else {
						for (iter = tabela_simbola.begin(); iter != tabela_simbola.end(); iter++)
							if (!(*iter)->name.compare("." + (*it)->section))break;
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*iter)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					break;
				}
			}
		}
	}

	if (indikator_bss != 0) {
		indikator_bss = abs(indikator_bss);
		simboli_bss.erase(simboli_bss.begin(), simboli_bss.begin() + (simboli_bss.size() - indikator_bss));//uklanjanje prvih par simbola koji ne prave suficit/deficit, znaci ako je
		for (brojac = simboli_bss.begin(); brojac < simboli_bss.end(); brojac++) {//bilo 4 simbola od kojih se 2 sabiraju i 2 oduzimaju i jos na to 2 koja se sabiraju, znaci prva 4 za koje ne
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {//trebaju relokacije ce biti ignorisani, posto je njihova razlika konstantna, a ova dvo ste sabiraju trebaju im
				if (!(*it)->name.compare(*brojac)) {//relokacioni zapisi jer zavise vrijednosti od adrese
					if ((*it)->binding == 'g') {//ako je globalni simbol uzmi njegov redni broj i upisi ga u relokacioni zapis, u suprotnom pronadji redni broj labele i upisi ga 
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*it)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);//stavi relokacioni zapis u odgovarajucu listu relokacionih zapisa (za tekucu sekciju)
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					else {
						for (iter = tabela_simbola.begin(); iter != tabela_simbola.end(); iter++)
							if (!(*iter)->name.compare("." + (*it)->section))break;
						rel_zapis* zap = new rel_zapis(l, "R_386_16", (*iter)->rb);
						if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);
						else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
						else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
					}
					break;
				}
			}
		}
	}


	if (vel == 2) {
		r->sadrzaj = r->sadrzaj & 0x0000ffff;//postavi gornje bitove na nulu
		r->sadrzaj = (r->sadrzaj >> 8) | (r->sadrzaj << 8);
		r->sadrzaj = r->sadrzaj & 0x0000ffff;
	}
	if (vel == 4) {
		r->sadrzaj = (logicalShiftR(r->sadrzaj,24) & 0xff) | // move byte 3 to byte 0
			((r->sadrzaj << 8) & 0xff0000) | // move byte 1 to byte 2
			(logicalShiftR(r->sadrzaj,8) & 0xff00) | // move byte 2 to byte 1
			((r->sadrzaj << 24) & 0xff000000); // byte 0 to byte 3
	}
	string str = "";
	if (vel == 1)r->sadrzaj = r->sadrzaj & 0x000000ff;

	if (vel == 1) {
		ss << std::hex << setfill('0') << setw(2) << r->sadrzaj;
		f = ss.str();
		ss.str(std::string());
	}
	else if (vel == 2) {
		ss << std::hex << setfill('0') << setw(4)<<r->sadrzaj;
		f = ss.str();
		ss.str(std::string());
	}
	else if (vel == 4) {
		ss << std::hex << setfill('0') << setw(8) << r->sadrzaj;
		f = ss.str();
		ss.str(std::string());
	}
	r->sadrzina = formatiraj_hex(f);
	if (r->sekc == "text")tabela_text.push_back(r);
	else if(r->sekc == "data")tabela_data.push_back(r);
	else if (r->sekc == "rodata")tabela_rodata.push_back(r);
}

void kodiranje_instrukcije(string s, bitset<16> *prvi) {
	if (regex_search(s, add)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 0);
		(*prvi).set(12, 0);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, sub)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 0);
		(*prvi).set(12, 0);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, mul)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 1);
		(*prvi).set(12, 0);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, divv)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 1);
		(*prvi).set(12, 0);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, cmp)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 0);
		(*prvi).set(12, 1);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, andd)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 0);
		(*prvi).set(12, 1);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, orr)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 1);
		(*prvi).set(12, 1);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, nott)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 1);
		(*prvi).set(12, 1);
		(*prvi).set(13, 0);
		return;
	}
	else if (regex_search(s, tst)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 0);
		(*prvi).set(12, 0);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, psh)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 0);
		(*prvi).set(12, 0);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, popp)|| regex_search(s,ret)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 1);
		(*prvi).set(12, 0);
		(*prvi).set(13, 1);
		vel_instr2 = 1;
		return;
	}
	else if (regex_search(s, call)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 1);
		(*prvi).set(12, 0);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, iret)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 0);
		(*prvi).set(12, 1);
		(*prvi).set(13, 1);
		vel_instr2 = 1;
		return;
	}
	else if (regex_search(s, mov)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 0);
		(*prvi).set(12, 1);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, shl)) {
		(*prvi).set(10, 0);
		(*prvi).set(11, 1);
		(*prvi).set(12, 1);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, shr)) {
		(*prvi).set(10, 1);
		(*prvi).set(11, 1);
		(*prvi).set(12, 1);
		(*prvi).set(13, 1);
		return;
	}
	else if (regex_search(s, jmp)) { 
		if (regex_search(s, pcrel)) {//kod za add
			(*prvi).set(10, 0);
			(*prvi).set(11, 0);
			(*prvi).set(12, 0);
			(*prvi).set(13, 0);
			}
		else if (regex_search(s,memdir)){//kod za mov
			(*prvi).set(10, 1);
			(*prvi).set(11, 0);
			(*prvi).set(12, 1);
			(*prvi).set(13, 1);
		}
		else {
			std::cout << "Kod jump instrukcije dozvoljeno samo pcrel i memdir adresiranje!Linija: " << broj_linije << endl;
			exit(1);
		}
		return;
	}

}


void generisi_zapis(bitset<16> *prvi, int vr, int vel) {
	unsigned long prvi_bajt = prvi->to_ulong();
	unsigned long lend1;
	int lend2;
	string prv = "";
	string drg = "";
	lend1 = (prvi_bajt >> 8) | (prvi_bajt << 8);
	lend1 = lend1 & 0x0000ffff; //konverzije u little endian
	if (vel == 2) {//ako instrukcija ima dvije rijeci potrebno je generisati i drugu rijec
		vr = vr & 0x0000ffff;
		lend2 = (vr >> 8) | (vr << 8);//gornji bajtovi ne uticu na donjih 16 prilikom pomjeranja
		lend2 = lend2& 0x0000ffff;
		ss << std::hex << setfill('0') << setw(4) << lend2;
		drg = ss.str();
		ss.str(std::string());
	}
	ss << std::hex << setfill('0') << setw(4) << lend1;
	prv = ss.str();
	ss.str(std::string());
	Sekcija *r = new Sekcija();
	r->sadrzaj = prvi_bajt;
	r->sekc = tekuca_sekcija;

	if(vel==2)//ako instrukcija ima dvije rijeci
	r->sadrzina = formatiraj_hex(prv + drg);
	else r->sadrzina = formatiraj_hex(prv);

	if (r->sekc == "text")tabela_text.push_back(r);
	else if (r->sekc == "data")tabela_data.push_back(r);
	else if (r->sekc == "rodata")tabela_rodata.push_back(r);
}

void zapisi_registar(bitset<16> *prvi, bool drugi,string s,int tip_adresiranja) {//postavlja bitove za registarska adresiranja, kao i odgovarajuce brojeve registara, indikator drugi omogucava da se razlikuje slucaj
	int vr;//kada je prvi operand registar, ili drugi operand
	string f = "";//tip_adresiranja: 0-regdir, 1 regindpom
	string z = "";
	regex_search(s, match, regdir);//pronadji registre 
	if (drugi&&(regex_search(s,regdir1)||regex_search(s,regpombr)||regex_search(s,regpomlab))) {
		f = match.suffix();
		regex_search(f, match, regdir);
	}

	f = match[0];
	switch (tip_adresiranja) {
		case 0: {//regdir
			if (drugi) {//postavi odgovarajuce oznake za odgovarajuci tip adresiranja i za odgovarajuci operand
			prvi->set(4, 0);
			prvi->set(3, 1);
			}
			else { prvi->set(9, 0); prvi->set(8, 1); }
			break;
		}
		case 1: {//regindpom
			if (drugi) {
				prvi->set(4, 1);
				prvi->set(3, 1);
			}
			else { prvi->set(9, 1); prvi->set(8, 1); }
			break;
		}
	
	}

	for (int i=0; i < f.length(); i++) {
		if (isdigit(f[i])) { z += f[i]; break; }//broj registra je jednocifren
	}
	vr = stoi(z);
	switch (vr) {
	case 0: {
		if (drugi) {
			prvi->set(0, 0);
			prvi->set(1, 0);
			prvi->set(2, 0);
		}
		else {
			prvi->set(5, 0);
			prvi->set(6, 0);
			prvi->set(7, 0);
		}
		break;
	}
	case 1: {
		if (drugi) {
			prvi->set(0, 1);
			prvi->set(1, 0);
			prvi->set(2, 0);
		}
		else {
			prvi->set(5, 1);
			prvi->set(6, 0);
			prvi->set(7, 0);
		}
		break;
	}
	case 2: {
		if (drugi) {
			prvi->set(0, 0);
			prvi->set(1, 1);
			prvi->set(2, 0);
		}
		else {
			prvi->set(5, 0);
			prvi->set(6, 1);
			prvi->set(7, 0);
		}
		break;
	}
	case 3: {
		if (drugi) {
			prvi->set(0, 1);
			prvi->set(1, 1);
			prvi->set(2, 0);
		}
		else {
			prvi->set(5, 1);
			prvi->set(6, 1);
			prvi->set(7, 0);
		}
		break;
	}
	case 4: {
		if (drugi) {
			prvi->set(0, 0);
			prvi->set(1, 0);
			prvi->set(2, 1);
		}
		else {
			prvi->set(5, 0);
			prvi->set(6, 0);
			prvi->set(7, 1);
		}
		break;
	}
	case 5: {
		if (drugi) {
			prvi->set(0, 1);
			prvi->set(1, 0);
			prvi->set(2, 1);
		}
		else {
			prvi->set(5, 1);
			prvi->set(6, 0);
			prvi->set(7, 1);
		}
		break;
	}
	case 6: {
		if (drugi) {
			prvi->set(0, 0);
			prvi->set(1, 1);
			prvi->set(2, 1);
		}
		else {
			prvi->set(5, 0);
			prvi->set(6, 1);
			prvi->set(7, 1);
		}
		break;
	}
	case 7: {
		if (drugi) {
			prvi->set(0, 1);
			prvi->set(1, 1);
			prvi->set(2, 1);
		}
		else {
			prvi->set(5, 1);
			prvi->set(6, 1);
			prvi->set(7, 1);
		}
		break;
	}
	}
	return;
}



void obradi_instrukciju(string s, bitset<16> *prvi) {
	int vr=0;//drugi bajt instrukcije
	string tip_relokacije = "";
	Elf_Symbol* simbol= new Elf_Symbol();
	string f = "";
	int vel = 2;
	int indikator = 1;
	int validno_adresiranje = 0;
	int lc1 = lc;
	int potrebna_relokacija = 1;
	if (regex_search(s, iret))indikator = 0;//indikator pokazuje treba li nesto jos upisivati ili ne
	if (indikator == 1) {

		if (regex_search(s, pcrel)) {
			validno_adresiranje = 1;
			tip_relokacije = "R_386_PC16";
			regex_search(s, match, pcrel);
			f = match[0];
			string z = "";

			for (int i = 0; i < f.size(); i++)
				if (isalnum(f[i]))z += f[i];
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
				if (!(*it)->name.compare(z)) {
					if (!(*it)->section.compare(tekuca_sekcija)) {//ako je jump instrukcija i ako je labela na koju se skace u tekucoj sekciji
						potrebna_relokacija = 0;//onda nije potreban relokacioni zapis, posto je pomjeraj konstantan
						vr = (*it)->value - lc;
						break;
					}
					else {
						if ((*it)->binding == 'g')vr = -2;
						else vr = (*it)->value - 2;
						simbol = (*it);
						break;
					}
				}
			}
			if (regex_search(s, pcrel1)|| regex_search(s, psh)||regex_search(s,jmp)) {//ako je prvi operand adresiran na pc relativno, postavi odgovarajuce bitove
				prvi->set(5, 1);
				prvi->set(6, 1);
				prvi->set(7, 1);//r7=pc
				if (regex_search(s, jmp)) { 
				prvi->set(8, 0);//ispravka
				prvi->set(9, 0);
				}
				else {
					prvi->set(8, 1);
					prvi->set(9, 1);//pcrel
				}
				if (!regex_search(s, psh) || regex_search(s, jmp))
				zapisi_registar(prvi, true, s, 0);

			}
			else if (regex_search(s, pcrel2)) {
					prvi->set(0, 1);
					prvi->set(1, 1);
					prvi->set(2, 1);
					prvi->set(3, 1);
					prvi->set(4, 1);
					zapisi_registar(prvi, false, s, 0);
				}
			
			generisi_zapis(prvi, vr, vel);
		}

		else if (regex_search(s, immed) && regex_search(s, psh) && !(regex_search(s,regdir ))) {//ovako radjeno posto regex immed registruje i regdir
			validno_adresiranje = 1;
			potrebna_relokacija = 0;
			regex_search(s, match, immed);
			prvi->set(8, 0);
			prvi->set(9, 0);
			f = match[0];
			vr = stoi(f);
			generisi_zapis(prvi, vr, vel);
		}

		else if (regex_search(s, immed2)) {
			validno_adresiranje = 1;
			potrebna_relokacija = 0;
			prvi->set(3, 0);//oznaka da je drugi operand neposredna vrijednost
			prvi->set(4, 0);
			regex_search(s, match, immed);
			f = match.suffix();
			regex_search(f, match, immed);
			f = match[0];//prvo poklapanje je sa brojem registra
			vr = stoi(f);
			zapisi_registar(prvi, false, s, 0);
			generisi_zapis(prvi, vr, vel);
			
		}

		else if (regex_search(s, regpombr)) {
			validno_adresiranje = 1;
			potrebna_relokacija = 0;
			string z = "";
			regex_search(s, match, regpombr);
			f = match[0];
			f = regex_replace(f, regdir, "");
			for (int i = 0; i < f.length(); i++)
				if (isdigit(f[i]))z += f[i];
			vr = stoi(z);
			if (regex_search(s, regpombr1) || regex_search(s, psh)) {
				zapisi_registar(prvi, false, s, 1);//prvi operand postavi registar na kojeg se odnosi adresiranje, kao i bitove za adresiranje
				if (!regex_search(s, psh))zapisi_registar(prvi, true, s, 0);//drugi operand postavi kao registarsko direktno adresiranje koje se odnosi na taj operand
			}
			else {
				zapisi_registar(prvi, false, s, 0);
				zapisi_registar(prvi, true, s, 1);
			}
			generisi_zapis(prvi, vr, vel);
		}

		else if (regex_search(s, regpomlab)) {
			validno_adresiranje = 1;
			string z = "";
			tip_relokacije = "R_386_16";
			regex_search(s, match, regpomlab);
			f = match[0];
			f = regex_replace(f, regdir, "");//ukloni registarsko direktno iz operacije
			for (int i = 0; i < f.length(); i++)
				if (isalnum(f[i]))z += f[i];
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
				if (!(*it)->name.compare(z)) {
					if ((*it)->binding != 'g') vr = (*it)->value;//ispravka
					simbol = (*it);
					break;
				}
			}
			if (regex_search(s, regpomlab1) || regex_search(s, psh)) {
				zapisi_registar(prvi, false, s, 1);//prvi operand postavi registar na kojeg se odnosi adresiranje, kao i bitove za adresiranje
				if (!regex_search(s, psh))zapisi_registar(prvi, true, s, 0);//drugi operand postavi kao registarsko direktno adresiranje koje se odnosi na taj operand
			}
			else {
				zapisi_registar(prvi, false, s, 0);
				zapisi_registar(prvi, true, s, 1);
			}
			generisi_zapis(prvi, vr, vel);

		}

		else if (regex_search(s, regdir1)|| regex_search(s, ret)|| (regex_search(s, psh) || regex_search(s, popp))) {
			validno_adresiranje = 1;
			potrebna_relokacija = 0;
			if(!regex_search(s,ret))zapisi_registar(prvi, false, s,0);
			if (regex_search(s, ret)) {
				prvi->set(5, 1);
				prvi->set(6, 1);
				prvi->set(7, 1);
				prvi->set(8, 1);
				prvi->set(9, 0);
			}
			if (!(regex_search(s, psh)||regex_search(s,popp)||regex_search(s,ret))) zapisi_registar(prvi, true, s,0);//u slucaju da nije neka od instrukcija koje imaju samo prvi operand, upisi drugi
			generisi_zapis(prvi, 0, 1);
		}

		
		else if (regex_search(s, constt)) {
		validno_adresiranje = 1;
		string z = "";
		tip_relokacije = "R_386_16";
		regex_search(s, match, constt);
		f = match[0];
		f = regex_replace(f, regdir, "");
		for (int i = 0; i < f.length(); i++)
			if (isalnum(f[i]))z += f[i];
		for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
			if (!(*it)->name.compare(z)) {
				if ((*it)->binding != 'g')vr = (*it)->value;
				simbol = (*it);
				break;
			}
		}
		if (regex_search(s, const1) || regex_search(s, psh)) {
			prvi->set(8, 0);
			prvi->set(9, 0);
			if (!regex_search(s, psh))zapisi_registar(prvi, true, s, 0);
		}
		else {
			prvi->set(3, 0);
			prvi->set(4, 0);
			zapisi_registar(prvi, false, s, 0);
		}
		generisi_zapis(prvi, vr, vel);
		}

		

		else if (regex_search(s, memind)) {
		validno_adresiranje = 1;
		potrebna_relokacija = 0;
		string z = "";
		regex_search(s, match, memind);
		f = match[0];
		f = regex_replace(f, regdir, "");
		for (int i = 0; i < f.length(); i++)
			if (isdigit(f[i]))z += f[i];
		vr = stoi(z);
		if (regex_search(s, memind1)||regex_search(s,psh)) {
			prvi->set(8, 0);
			prvi->set(9, 1);
			if (!regex_search(s, psh))zapisi_registar(prvi, true, s, 0);
		}
		else {
			prvi->set(3, 0);
			prvi->set(4, 1);
			zapisi_registar(prvi, false, s, 0);
		}
		generisi_zapis(prvi, vr, vel);
		}

		else if ((regex_search(s, memdir)&&regex_search(s,psh))||regex_search(s,memdir1)||regex_search(s,memdir2)||regex_search(s,call)||regex_search(s,jmp)) {
		validno_adresiranje = 1;
		string z = "";
		bool pronadjen_simbol = false;
		tip_relokacije = "R_386_16";
		regex_search(s, match, memdir);
		f = match.suffix();
		regex_search(f, match, memdir);
		if (regex_search(s, memdir1) || regex_search(s, psh) || regex_search(s, popp) || regex_search(s, call) || regex_search(s, jmp)) {
			f = match[0];
			f = regex_replace(f, regdir, "");
		}
		else {
			f = match.suffix();
			regex_search(f, match, memdir);
			f = match[0];
		}
		for (int i = 0; i < f.length(); i++)
			if (isalnum(f[i]))z += f[i];
		for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
			if (!(*it)->name.compare(z)) {
				vr = (*it)->value;
				simbol = (*it);
				pronadjen_simbol = true;
				break;
			}
		}
		if (!pronadjen_simbol) {//za call instrukciju, ako ne nadje simbol, dodaje ga u tabelu i postavi parametre za relokativni zapis
			Elf_Symbol *novi = new Elf_Symbol(z, 0, 0, 'g', "UND", 'd');
			novi->rb = tabela_simbola.size()+1;
			tabela_simbola.push_back(novi);
			vr = -2;
			simbol = novi;
		}
		if (regex_search(s, memdir1) || regex_search(s, psh) || regex_search(s, popp) || regex_search(s, call) || regex_search(s, jmp)) {
			prvi->set(8, 0);
			if (regex_search(s, jmp)||regex_search(s,call))prvi->set(9, 0);
			else prvi->set(9, 1);
			if (!(regex_search(s, psh) || regex_search(s, popp) || regex_search(s, call) || regex_search(s, jmp)))zapisi_registar(prvi, true, s, 0);
		}
		else {
			prvi->set(3, 0);
			prvi->set(4, 1);
			zapisi_registar(prvi, false, s, 0);
		}
		generisi_zapis(prvi, vr, vel);
		}

		else { std::cout << "Greska u adresiranju na liniji: " << broj_linije << endl; exit(1); }



		if (potrebna_relokacija==1) {
			rel_zapis* zap;
			if (simbol->binding == 'g') {
				zap = new rel_zapis(lc1-2,tip_relokacije,simbol->rb);
			}
			else {
				for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) 
					if (!(*it)->section.compare(simbol->section)) {//moze ovako posto se u tabeli simbola nalaze prvo sekcije pa onda podaci, tako da ne treba provjeravati ime;
						zap = new rel_zapis(lc1 - 2, tip_relokacije, (*it)->rb);
						break;
					}
			}
			if (!tekuca_sekcija.compare("data"))rel_data.push_back(zap);//stavi relokacioni zapis u odgovarajucu listu relokacionih zapisa (za tekucu sekciju)
			else if (!tekuca_sekcija.compare("text"))rel_text.push_back(zap);
			else if (!tekuca_sekcija.compare("rodata"))rel_rodata.push_back(zap);
		}

	}
}


bool manje(Elf_Symbol *a, Elf_Symbol *b) {
	if (a->rb < b->rb)return true;
	else return false;
}

int main() {
	bitset<16> prvi;
	std::cout << "Unesite naziv tekstualnog fajla bez ekstenzije\n";
	cin >> s;
	s += ".txt";
	Elf_Symbol* simbol;
	Elf_Symbol* za_sekciju;
	//regexi za sekcije:
	regex text(".text"); regex rodata(".rodata"); regex data(".data"); regex bss(".bss");
	//regex za labele
	regex lab("\\w+:");

	ifstream ulaz;
	try {
		ulaz.open(s);
	}
	catch (exception e) {
		std::cout << "Ne postoji fajl sa datim imenom";
		exit(1);
	}
	//prvi prolaz:
	cout << "Unesite pocetnu adresu\n";
	cin >> pocetna_adresa;
	string za_poredjenje = "";
	while (getline(ulaz, s)) {
		broj_linije++;
		if (s == ".end")break;
			//sekcije
		if (regex_search(s, text)) {
				simbol = new Elf_Symbol(".text", 0, 0, 'l', "text",'s');
				za_poredjenje = "." + tekuca_sekcija;
				lc2 += lc;
				if (!tabela_simbola.empty()) {
					for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++)
						if (!(*it)->name.compare(za_poredjenje)) {
							(*it)->size = lc;
							simbol->value = lc2 + pocetna_adresa;
							break;
						}

				}
				tabela_simbola.push_back(simbol);
				tekuca_sekcija = "text";
				lc = 0;
				br_sekcija++;
			}
		else if (regex_search(s, rodata)) {
				simbol = new Elf_Symbol(".rodata", 0, 0, 'l', "rodata", 's');
				lc2 += lc;
				za_poredjenje = "." + tekuca_sekcija;
				if (!tabela_simbola.empty()) {
					for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++)
						if (!(*it)->name.compare(za_poredjenje)) {
							(*it)->size = lc;
							simbol->value = lc2 + pocetna_adresa;
							break;
						}

				}
				tabela_simbola.push_back(simbol);
				tekuca_sekcija = "rodata";
				lc = 0;
				br_sekcija++;

			}
		else if (regex_search(s, bss)) {
				simbol = new Elf_Symbol(".bss", 0, 0, 'l', "bss", 's');
				lc2 += lc;
				za_poredjenje = "." + tekuca_sekcija;
				if (!tabela_simbola.empty()) {
					for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++)
						if (!(*it)->name.compare(za_poredjenje)) {
							(*it)->size = lc;
							simbol->value = lc2 + pocetna_adresa;
							break;
						}

				}
				tabela_simbola.push_back(simbol);
				tekuca_sekcija = "bss";
				lc = 0;
				br_sekcija++;
			}
		else if (regex_search(s, data)) {
				simbol = new Elf_Symbol(".data", 0, 0, 'l', "data", 's');
				lc2 += lc;
				za_poredjenje = "." + tekuca_sekcija;
				if (!tabela_simbola.empty()) {
					for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++)
						if (!(*it)->name.compare(za_poredjenje)) {
							(*it)->size = lc;
							simbol->value = lc2 + pocetna_adresa;
							break;
						}

				}
				tabela_simbola.push_back(simbol);
				tekuca_sekcija = "data";
				lc = 0;
				br_sekcija++;

			}
		else if (regex_search(s, global)) {
				s=regex_replace(s, global, "");
				string f = "";
			for (int i = 0; i < s.length()+1; i++) {
				if (isalnum(s[i])) {
					f +=  s[i];
					}
				else {
					if (f != "") {
						simbol = new Elf_Symbol(f, 0, 0, 'g', "UND", 'd');
						tabela_simbola.push_back(simbol);
					}
					f = "";
				}
				}
			}
		//labele
		else if (regex_search(s, lab)) {
			string f = "";
			int flag = 0;
			for (int i = 0; i < s.length(); i++) {
				if (isalnum(s[i]) || s[i] == '_')f += s[i];
				else if (s[i] == ':')break;
			}
			for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
				if (!(*it)->name.compare(f)) {
					flag = 1;
					(*it)->section = tekuca_sekcija;
					(*it)->value = lc;
					break;
				}
			}
			if (flag == 0) {
				simbol = new Elf_Symbol(f, lc, 0, 'l', tekuca_sekcija, 'd');
				tabela_simbola.push_back(simbol);
			}
			pretraga_na_direktivu(s);
			if (ind_instrukcija)
				pretraga_na_instrukciju(s);
		}
		else if (!s.compare("") || (s.find_first_not_of(' ') == std::string::npos) || (!s.compare("\t")))continue;//ako je prazan red, preskace se
		else {//direktive i instrukcije u prvom prolazu
			pretraga_na_direktivu(s);
			if(ind_instrukcija)
			pretraga_na_instrukciju(s);
			
		}
		ind_instrukcija = 1;

		}
	
	ofstream ispis;

	rb_simbola = br_sekcija + 1;
	for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
		if ((*it)->type == 's')(*it)->rb = rb_sekcije++;
		else (*it)->rb = rb_simbola++;
	}
	tabela_simbola.sort(manje);
	lc2 += lc;
	za_poredjenje = "." + tekuca_sekcija;

	for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {//postavljanje adrese prvoj sekciji
		if ((*it)->rb==1) {
			(*it)->value = pocetna_adresa;
		}
	}
	for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {//postavljanje velicine poslednjoj sekciji i vrijednosti
		if (!(*it)->name.compare(za_poredjenje)) {
			(*it)->size = lc;
			(*it)->value = lc2 - lc + pocetna_adresa;
		}
	}

	//drugi prolaz asemblera
	lc = 0;
	broj_simbola_u_labeli = 0;
	za_skip.clear();
	za_align.clear();
	ulaz.seekg(0, ios::beg);
	broj_linije=0;

	while (getline(ulaz, s)) {
		broj_linije++;
		prvi.reset();
		if (!s.compare(".end"))break;
		int lc1;
		//ne obradjuje se u drugom prolazu
		if(!s.compare("") || (s.find_first_not_of(' ') == std::string::npos) || (!s.compare("\t")))continue;
		else if (regex_search(s, text)) {
			tekuca_sekcija = "text"; lc = 0;
		}
		else if (regex_search(s, rodata)) { tekuca_sekcija = "rodata"; lc = 0; ind_instrukcija = 0; }
		else if (regex_search(s, data)) { tekuca_sekcija = "data"; lc = 0; ind_instrukcija = 0;
		}
		else if (regex_search(s, bss)){tekuca_sekcija = "bss"; lc = 0; ind_instrukcija = 0;
		}
		else if (regex_search(s, global))continue;
		else {
			if (regex_search(s, lab)) {
				s = regex_replace(s, lab, "");
				if (!s.compare("") || (s.find_first_not_of(' ') == std::string::npos) || (!s.compare("\t"))) {
					ind_instrukcija = 1; continue;
				}//ako je prazno nastavi
			}
			lc1 = lc;
			pretraga_na_direktivu(s);
			if (ind_instrukcija == 0) {
				switch (indikator) {
				case 0: {//char
					string f = "";
					lc1 = lc - broj_simbola_u_labeli;
					s = regex_replace(s, ch, "");
					for (int i = 0; i < s.length(); i++) {
						if (isalnum(s[i]) || s[i] == '_')f += s[i];
						else if (s[i] == '+' || s[i] == '-')f += s[i];
						else if (s[i] == ',') {
						Sekcija* sec = new Sekcija();
						sec->sekc = tekuca_sekcija;
						obradi_labelu(f, sec, lc1, 1);
						lc1++;
						f = "";
						}
					}
					Sekcija* sec = new Sekcija();
					sec->sekc = tekuca_sekcija;
					obradi_labelu(f, sec, lc1, 1);
					lc1++;
					f = "";
					broj_simbola_u_labeli = 0;
					break;
				}
				case 1: {//long
					string f = "";
					s = regex_replace(s,lo, "");
					lc1 = lc - broj_simbola_u_labeli*4;
					for (int i = 0; i < s.length(); i++) {
						if (isalnum(s[i]) || s[i] == '_')f += s[i];
						else if (s[i] == '+' || s[i] == '-')f += s[i];
						else if (s[i] == ',') {
							Sekcija* sec = new Sekcija();
							sec->sekc = tekuca_sekcija;
							obradi_labelu(f, sec, lc1, 4);
							lc1+=4;
							f = "";
						}
					}
					Sekcija* sec = new Sekcija();
					sec->sekc = tekuca_sekcija;
					obradi_labelu(f, sec, lc1, 4);
					lc1 += 4;
					f = "";
					broj_simbola_u_labeli = 0;
					break;
				}
				case 2: {//word
					string f = "";
					s = regex_replace(s, word, "");
					lc1 = lc - 2 * broj_simbola_u_labeli;
					for (int i = 0; i < s.length(); i++) {
						if (isalnum(s[i]) || s[i] == '_')f += s[i];
						else if (s[i] == '+' || s[i] == '-')f += s[i];
						else if (s[i] == ',') {
							Sekcija* sec = new Sekcija();
							sec->sekc = tekuca_sekcija;
							obradi_labelu(f, sec, lc1, 2);
							lc1 += 2;
							f = "";
						}
					}
					Sekcija* sec = new Sekcija();
					sec->sekc = tekuca_sekcija;
					obradi_labelu(f, sec, lc1, 2);
					lc1 += 2;
					f = "";
					broj_simbola_u_labeli = 0;
					break;
					}
				case 3: case 4: {//skip i align
					Sekcija* sec = new Sekcija();
					sec->tip = "s/a";
					sec->sekc = tekuca_sekcija;
					obradi_labelu(s, sec, lc1,0);
					break;
					}
				}
				
			}
			else{
			//prvo provjera za uslove eq,ne,gt,al(apsolutno uvijek izvrsi), napraviti niz bitova pa ih na osnovu toga popuniti
				if (regex_search(s, eq)) {
					prvi.set(15, 0); prvi.set(14, 0);
				}
				else if (regex_search(s, ne)) {
					prvi.set(15, 0); prvi.set(14, 1);
				}
				else if (regex_search(s, gt)) {
					prvi.set(15, 1); prvi.set(14, 0);

				}
				else {
					prvi.set(15, 1); prvi.set(14, 1);
				}
			//zatim provjera naziva instrukcije i na osnovu toga popuniti sledeca 4 bita opcode
				pretraga_na_instrukciju(s);//da bi se povecao lc
				kodiranje_instrukcije(s, &prvi);
				obradi_instrukciju(s, &prvi);

			//nakon toga krece citanje operanada sa regexima i na osnovu toga se popunjava ostatak instrukcije, i prave se relokacioni zapisi
			//u slucaju call instrukcije obratiti paznju na poziv funkcije, dodati je u tabelu simbola kao globalni simbol
			}
			ind_instrukcija = 1;
		}

	}
	//provjere za sekcije i relokacije

	ispis.open("izlaz.txt");
	ispis << left << "#Tabela simbola\n";
	ispis << left << setw(12) << "#ime" << setw(12) << "#sekcija" << setw(12) << "#vr" << setw(12) << "#dostupnost" << setw(12) << "#rb" << endl;
	ispis << left << setw(12) << "UND " << setw(12) << 0 << setw(12) << "l " << 0 << setw(12) << endl;

	for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
		ispis << left << setw(12) << (*it)->name << setw(12) << (*it)->section << setw(12) << (*it)->value << setw(12) << (*it)->binding << setw(12) << (*it)->rb << endl;
	}


	ispis << left << "\n#Sekcije i njihove velicine\n";
	for (it = tabela_simbola.begin(); it != tabela_simbola.end(); it++) {
		if((*it)->type=='s')ispis << left << setw(12) << (*it)->name << setw(12) << (*it)->size << endl;
	}

	if (!tabela_text.empty()) {
		ispis << left << "\n#.text\n";
		for (iter = tabela_text.begin(); iter != tabela_text.end(); iter++) {
			ispis << left;
			if ((*iter)->tip.compare("s/a"))ispis << setw(12);
			ispis << (*iter)->sadrzina << endl;
		}
	}

	if (!tabela_data.empty()) {
		ispis << left << "\n.#data\n" << endl;
		for (iter = tabela_data.begin(); iter != tabela_data.end(); iter++) {
			ispis << left;
			if((*iter)->tip.compare("s/a"))ispis << setw(12);
			ispis<< (*iter)->sadrzina << endl;
		}
	}

	if (!tabela_rodata.empty()) {
		ispis << left << "\n.#rodata\n" << endl;
		for (iter = tabela_rodata.begin(); iter != tabela_rodata.end(); iter++) {
			ispis << left;
			if ((*iter)->tip.compare("s/a"))ispis << setw(12);
			ispis << (*iter)->sadrzina << endl;
		}
	}

	if(!rel_text.empty()){
		ispis << left << "\n#.rel.text\n" << endl;
		for (it_rel = rel_text.begin(); it_rel != rel_text.end(); it_rel++) {
			ispis<< left << setw(12) << (*it_rel)->offset << setw(12) << (*it_rel)->tip << setw(12) << (*it_rel)->rb << endl;
		}
	}
	if (!rel_data.empty()) {
		ispis << left << "\n#.rel.data" << endl;
		for (it_rel = rel_data.begin(); it_rel != rel_data.end(); it_rel++) {
			ispis << left << setw(12) << (*it_rel)->offset << setw(12) << (*it_rel)->tip << setw(12) << (*it_rel)->rb << endl;
		}
	}

	if (!rel_rodata.empty()) {
		ispis << left << "\n#.rel.rodata" << endl;
		for (it_rel = rel_rodata.begin(); it_rel != rel_rodata.end(); it_rel++) {
			ispis << left << setw(12) << (*it_rel)->offset << setw(12) << (*it_rel)->tip << setw(12) << (*it_rel)->rb << endl;
		}
	}
	ispis.close();
	cout << "Uspjesno prevodjenje! Rezultat prevodjenja je u izlaz.txt!\n";
}

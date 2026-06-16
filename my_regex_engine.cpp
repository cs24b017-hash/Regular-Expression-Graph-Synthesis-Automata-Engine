#include<bits/stdc++.h>
using namespace std;

//GRAPH NODE
class State{
    public:
    int id;
    bool isAccept;
    vector<pair<char,State*>> transition;
    vector<State*> epsilonTransition;
    State(int uniqueid) :id(uniqueid),isAccept(false){}
};

//used to keep track of all the states space and used while deleting all the states.

class AutomatonContext{
    private:
    int stateCounter = 0;
    vector<State*> allstates;
    public:
    State* createState(){
        State* temp = new State(++stateCounter);
        allstates.push_back(temp);
        return temp;        
    }

    ~AutomatonContext(){
        for(auto &f:allstates){ // here just  be carefull
            delete f;
        }
    
    }
};

struct NFAstruct{
    State* start;
    State* accept;
};

class Parser{
    private:
    bool isOperand(char ch){
        return isalnum(ch) || ch == '@' || ch =='.';
    }
    string insertConcatop(string &regex){//not a const
        string res = "";
        for(int i =0;i<regex.size();i++){
            char ch1 = regex[i];
            res += ch1;
            if(i + 1 < regex.size()){
                char ch2 = regex[i+1];
                    if ((isOperand(ch1) && isOperand(ch2)) ||
                    (isOperand(ch1) && ch2 == '(') ||
                    (ch1 == ')' && isOperand(ch2)) ||
                    (ch1 == '*' && isOperand(ch2)) ||
                    (ch1 == '*' && ch2 == '(') ||
                    (ch1 == ')' && ch2 == '(')) {
                    res += '\x01'; 
                }
            }
        }
        return res;
    }
    int getprec(char ch){
        if(ch == '*')return 3;
        if(ch == '\x01')return 2;
        if(ch == '|')return 1;
        return 0;
    }
    public:
    string infixToPostfix(string &infix, set<char> &usedAplhabet){
        string modified_infix = insertConcatop(infix);
        string postfix = "";
        stack<char> st;
        for(auto &ch:modified_infix){ // few namings
            if(isOperand(ch)){
                postfix += ch;
                usedAplhabet.insert(ch);
            }
            else if(ch =='('){
                st.push('(');
            }
            else if(ch == ')'){
                while(!st.empty() && st.top()!='('){
                    postfix += st.top();
                    st.pop();
                }
                if(!st.empty())st.pop();
            }
            else {
                while(!st.empty() && getprec(st.top()) >= getprec(ch)){
                    postfix += st.top();
                    st.pop();
                }
                st.push(ch);
            }
        }
        while(!st.empty()){
            postfix += st.top();
            st.pop();
        }
        return postfix;
    }

};

//NFA BUILDER
class NFABuilder{
    private:
    static bool isoperand(char ch){//it was static
        return isalnum(ch) || ch =='@' || ch == '.';
    }
    public:
    static NFAstruct buildNFA(string &postfix,AutomatonContext &ctx){
        stack<NFAstruct> st;
        for(auto &ch:postfix){
            if(isoperand(ch)){
                State* start = ctx.createState();
                State* accept = ctx.createState();
                accept -> isAccept = true;
                start->transition.push_back({ch,accept});
                st.push({start,accept});
            }
            else if(ch =='*'){
                if(st.empty()){
                    throw runtime_error("Malformed Regex: Stack underflow on '*'.");//no idea wt this is
                }
                NFAstruct  f = st.top();
                st.pop();
                State* start = ctx.createState();
                State* accept = ctx.createState();
                accept->isAccept = true;
                f.accept ->isAccept = false;
                start->epsilonTransition.push_back(accept);
                start -> epsilonTransition.push_back(f.start);
                f.accept -> epsilonTransition.push_back(f.start);
                f.accept ->epsilonTransition.push_back(accept);
                st.push({start,accept});
            }
            else if(ch =='\x01'){
                if (st.size() < 2) throw runtime_error("Malformed Regex: Stack underflow on Concat.");
                NFAstruct b = st.top();
                st.pop();
                NFAstruct a = st.top();
                st.pop();
                a.accept -> isAccept = false;
                a.accept ->epsilonTransition.push_back(b.start);
                st.push({a.start,b.accept});
            }
            else if(ch == '|'){
                if (st.size() < 2) throw runtime_error("Malformed Regex: Stack underflow on Union.");
                NFAstruct b = st.top();
                st.pop();
                NFAstruct a = st.top();
                st.pop();
                State* start = ctx.createState();
                State* accept = ctx.createState();

                b.accept ->isAccept = false;
                a.accept ->isAccept = false;
                accept -> isAccept = true;

                start->epsilonTransition.push_back(a.start);
                start->epsilonTransition.push_back(b.start);
                a.accept->epsilonTransition.push_back(accept);
                b.accept->epsilonTransition.push_back(accept);
                st.push({start,accept});
            }
        }
        if (st.empty()) throw runtime_error("Malformed Regex: Empty compilation stack.");
        return st.top();
    }
};

//DFA 
struct DFAState{
    int id;
    bool isAccept = false;
    map<char,DFAState*> transitions;
};

class DFAengine{
    private:
    vector<DFAState*> dfaAllStates;
    DFAState* dfaStartNode = nullptr;    
    void getEpsilonClosure(State* state, set<State*>& closure) {
        if (closure.count(state)) return;
        closure.insert(state);
        for (State* next : state->epsilonTransition) {
            getEpsilonClosure(next, closure);
        }
    }
    set<State*> computeClosureOfSet(const set<State*>& nfaStates) {
        set<State*> closure;
        for (State* s : nfaStates) {
            getEpsilonClosure(s, closure);
        }
        return closure;
    }
    void clearPool() {
        for (DFAState* ds : dfaAllStates) {
            delete ds;
        }
        dfaAllStates.clear();
        dfaStartNode = nullptr;
    }
    public:
    ~DFAengine(){
        clearPool();
    }
    void convertFromNFA(NFAstruct nfa, const set<char>& alphabet) {
        clearPool(); //For new NFA
    
        map<set<State*>, DFAState*> subsetMap;
        queue<set<State*>> pq;

        set<State*> initialClosure = computeClosureOfSet({nfa.start});
        
        DFAState* startDFAState = new DFAState();
        startDFAState->id = 0;
        dfaStartNode = startDFAState;
        dfaAllStates.push_back(startDFAState);
        
        subsetMap[initialClosure] = dfaStartNode;
        pq.push(initialClosure);

        int idGen = 1;

        while (!pq.empty()) {
            set<State*> currentNFAStates = pq.front();
            pq.pop();
            
            DFAState* currentDFAState = subsetMap[currentNFAStates];

            for (State* s :currentNFAStates) {
                if (s->isAccept) {
                    currentDFAState->isAccept = true;
                    break;
                }
            }

            for (char symbol :alphabet) {
                set<State*> targetNFAStates;
                
                for (State* s : currentNFAStates) {
                    for (auto& trans : s->transition) {
                        if (trans.first == symbol) {
                            targetNFAStates.insert(trans.second);
                        }
                    }
                }

                set<State*> moveClosure = computeClosureOfSet(targetNFAStates);
                if (moveClosure.empty()) continue;

                if (subsetMap.find(moveClosure) == subsetMap.end()) {
                    DFAState* newDFAState = new DFAState();
                    newDFAState->id = idGen++;
                    subsetMap[moveClosure] = newDFAState;
                    pq.push(moveClosure);
                    dfaAllStates.push_back(newDFAState); // Pushed directly as a raw pointer
                }

                currentDFAState->transitions[symbol] = subsetMap[moveClosure];
            }
        }
    }

    bool evaluate(string& input) {
        if (!dfaStartNode) return false;
        DFAState* current = dfaStartNode;
        for (char c :input) {
            if (current->transitions.find(c) == current->transitions.end()) {
                return false; 
            }
            current = current->transitions[c];
        }
        return current->isAccept;
    }    
};

int main(){
while (true) {
        string rawRegex;
        cout << "Enter a Regular Expression Pattern (or type 'exit' to quit):\n";
        cout << "Supported features: Literals, (Parentheses), * (Star), | (Union)\n\n";
        cout << "Regex> ";
        if (!getline(cin, rawRegex) || rawRegex == "exit") {
            break;
        }

        if (rawRegex.empty()) {
            continue;
        }
        {
            AutomatonContext memoryContext; 
            Parser parser;
            set<char> machineAlphabet;

            string postfix = parser.infixToPostfix(rawRegex, machineAlphabet);
            //NFA Generation Complete
            NFAstruct nfaGraph = NFABuilder::buildNFA(postfix, memoryContext);
            DFAengine engine;

            //DFA Subset Construction
            engine.convertFromNFA(nfaGraph, machineAlphabet);
            cout << "Enter text strings to test against the pattern.\n";
            cout << "Type 'new' to change the regex pattern, or 'exit' to quit.\n\n";

            while (true) {
                string testString;
                cout << "Match Text> ";
                if (!getline(cin, testString)) break;

                if (testString == "new") {
                    cout << "---------------------------------------------------\n";
                    break; 
                }
                if (testString == "exit") {
                    cout << "Exiting regex engine :)\n";
                    return 0; 
                }

                bool isAMatch = engine.evaluate(testString);
                cout << "Result    > " << (isAMatch ? "\033[1;32m[MATCH]\033[0m" : "\033[1;31m[NO MATCH]\033[0m") << "\n\n";
            }
        }
    }
    cout << "Exiting regex engine :) \n";
    return 0;
}
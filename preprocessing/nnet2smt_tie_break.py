import sys
from decimal import Decimal

my_file = "heart_attack/heart_attack_50x2.nnet"
translated_file = "../bench_XAI_ha/heart_attack_50x2.smt2"
original_sample = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]


binary_classification = True
multiclass_classification = not binary_classification

which_class = 0

def read_nnet(NNnnet):
    file_lines = []
    with open(NNnnet,"r") as g:
        for line in g:
            file_lines.append(line)
    return file_lines

def polish_file_lines(file_lines):
    polished = []
    for i in range(len(file_lines)):
        if (file_lines[i][0]!="/" or file_lines[i][1]!="/"):
            polished.append(file_lines[i])
            
    return polished
    
def next_comma(s,i):
    for j in range(len(s)):
        if (j>=i and s[j]==","):
            return j
            
def from_first_line(file_lines):
    a = next_comma(file_lines[0],0)
    b = next_comma(file_lines[0],a+1)
    c = next_comma(file_lines[0],b+1)
    d = next_comma(file_lines[0],c+1)
    
    nl = int(file_lines[0][0:a])
    ni = int(file_lines[0][a+1:b])
    no = int(file_lines[0][b+1:c])
    mls = int(file_lines[0][c+1:d])
    
    return nl, ni, no, mls

def from_second_line(file_lines):
    # Get first number of layers
    a = next_comma(file_lines[0],0)
    nl = int(file_lines[0][0:a])
    
    NN = []
    previous_comma = -1
    # Obtain NN architecture
    for i in range(nl+1):
        b = next_comma(file_lines[1],previous_comma+1)
        NN.append(int(file_lines[1][previous_comma+1:b]))
        previous_comma = b
        
    return NN
    
def get_W(file_lines,NN_architecture,maximum_layer_size):
    W = []
    
    origin_W_line = 7
    # Notice len(NN_architecture)-1 = number_layers
    for a in range(len(NN_architecture)-1):
        X = []
        added_x = 0
        for i in range(origin_W_line,origin_W_line+NN_architecture[a+1]):
            p = []
            previous_comma = -1
            added_values = 0
            for j in range(NN_architecture[a]):
                b = next_comma(file_lines[i],previous_comma+1)
                p.append(float(file_lines[i][previous_comma+1:b]))
                added_values+=1
                previous_comma = b
            while(added_values<maximum_layer_size):
                p.append(0.0)
                added_values+=1
            X.append(p)
            added_x += 1
        while(added_x<maximum_layer_size):
            p = []
            for k in range(maximum_layer_size):
                p.append(0.0)
            X.append(p)
            added_x+=1
        W.append(X)
        origin_W_line += 2*NN_architecture[a+1]
        
    return W

def get_b(file_lines,NN_architecture,maximum_layer_size):
    b = []
    
    origin_b_line = 7+NN_architecture[1]
    for a in range(len(NN_architecture)-1):
        x = []
        added_x = 0
        for i in range(origin_b_line,origin_b_line+NN_architecture[a+1]):
            p = next_comma(file_lines[i],0)
            x.append(float(file_lines[i][0:p]))
            added_x+=1
        while(added_x<maximum_layer_size):
            x.append(0.0)
            added_x+=1
        b.append(x)
        if (a+2<=len(NN_architecture)-1):
            origin_b_line += NN_architecture[a+1]+NN_architecture[a+2]

    return b
    
        


def write_decl(f,x,number_layers):
    f.write("(declare-var counter Real)\n")
    f.write("(declare-var counter_prime Real)\n")
    c = "((Real)"
    for i in range(x):
        f.write("(declare-var x"+str(i)+" Real)\n")
        c+="(Real) "
    for i in range(x):
        f.write("(declare-var x"+str(i)+"_prime Real)\n")
    for i in range(x):
        f.write("(declare-var w"+str(i)+" (Array Real (Array Real Real)))\n")
        c+="(Array Real (Array Real Real)) "
        
    for i in range(x):
        f.write("(declare-var w"+str(i)+"_prime (Array Real (Array Real Real)))\n")
        
    for i in range(x):
        f.write("(declare-var b"+str(i)+" (Array Real Real))\n")
        if (i!=x-1):
            c+="(Array Real Real) "
        else:
            c+="(Array Real Real)"
    
    for i in range(x):
        f.write("(declare-var b"+str(i)+"_prime (Array Real Real))\n")
       
        
    c+=")"
    
   
    
    #(define-fun ReLU ((a Real) (b Real) (c Real)) Real (ite (= c 1) a (max a b)))
    
    x = "(define-fun max ((a Real) (b Real)) Real (ite (> a b) a b))\n"
    f.write(x)
    
    x = "(define-fun ReLU ((a Real) (b Real) (c Real)) Real (ite (= c "+str(number_layers-1)+") a (max a b)))\n"
    f.write(x)
    
    # ------------------------------------------------------------------------------------- #
    
    
    
    
    f.write("(declare-rel inv "+c+")\n")
    f.write("(declare-rel fail ())\n")
    
def write_decl_no_fix(f,x,number_layers):
    f.write("(declare-var counter Real)\n")
    f.write("(declare-var counter_prime Real)\n")
    c = "((Real)"
    for i in range(x):
        f.write("(declare-var x"+str(i)+" Real)\n")
        c+="(Real) "
    for i in range(x):
        f.write("(declare-var x"+str(i)+"_prime Real)\n")
    for i in range(x):
        f.write("(declare-var w"+str(i)+" (Array Real (Array Real Real)))\n")
        c+="(Array Real (Array Real Real)) "
        
    for i in range(x):
        f.write("(declare-var w"+str(i)+"_prime (Array Real (Array Real Real)))\n")
        
    for i in range(x):
        f.write("(declare-var b"+str(i)+" (Array Real Real))\n")
        if (i!=x-1):
            c+="(Array Real Real) "
        else:
            c+="(Array Real Real)"
    
    for i in range(x):
        f.write("(declare-var b"+str(i)+"_prime (Array Real Real))\n")
       
        
    c+=")"
    

    
    # ------------------------------------------------------------------------------------- #
    
    
    
    
    f.write("(declare-rel inv "+c+")\n")
    f.write("(declare-rel fail ())\n")
    

    
def to_plain(x):
    
    # AVOID STOI error
    if (x>=0 and x<= 0.0001):
        x = 0
    
    if (x<=0 and x>=-0.0001):
        x = 0
        
    d = Decimal(x if isinstance(x, str) else str(x))
    return format(d, "f")

def write_header(f,x,number_layers,W,b):
    f.write("\n")
    f.write("(rule\n")
    f.write("\t(=>\n")
    f.write("\t\t(and\n")
    for i in range(x):
        f.write("\t\t\t(= x"+str(i)+" "+str(original_sample[i])+")\n")
    f.write("\t\t\t(= counter 0)\n")
    
    for i in range(number_layers):
        for j in range(x):
            for k in range(x):
                f.write("\t\t\t(= (select (select w"+str(j)+" "+str(k)+") "+str(i)+") "+to_plain(W[i][j][k])+")\n")
                    
    for i in range(number_layers):
        for j in range(x):
            f.write("\t\t\t(= (select b"+str(j)+" "+str(i)+") "+to_plain(b[i][j])+")\n")
    
    f.write("\t\t)\n")
    
    c = ""
    
    for i in range(x):
        c+="x"+str(i)+" "
    
    for i in range(x):
        c+="w"+str(i)+" "
        
    for i in range(x):
        if (i!=x-1):
            c+="b"+str(i)+" "
        else:
            c+="b"+str(i)
    
    f.write("\t\t(inv counter "+c+")\n")
    
    f.write("\t)\n")
    f.write(")\n")
    
def write_transition(f,x,number_layers):
    f.write("\n")
    f.write("(rule\n")
    f.write("\t(=>\n")
    f.write("\t\t(and\n")
    
    c = ""
    for i in range(x):
        c+="x"+str(i)+" "

    for i in range(x):
        c+="w"+str(i)+" "
    
    for i in range(x):
        if (i!=x-1):
            c+="b"+str(i)+" "
        else:
            c+="b"+str(i)

    f.write("\t\t\t(inv counter "+c+")\n")
    
    # write transition
    for i in range(x):
        c = "(+ "
        
        for j in range(x):
            c+="(* (select (select w"+str(i)+" "+str(j)+") counter) x"+str(j)+") "
        
        
        c+="(select b"+str(i)+" counter"+")"
        
        c+=")"
        f.write("\t\t\t(= x"+str(i)+"_prime (ReLU "+c+" 0 counter))\n")
    
    # copy weights and biases
    for i in range(x):
        f.write("\t\t\t(= w"+str(i)+"_prime w"+str(i)+")\n")
    
    for i in range(x):
        f.write("\t\t\t(= b"+str(i)+"_prime b"+str(i)+")\n")
    
    f.write("\t\t\t(= counter_prime (+ counter 1))\n")
    
    c=""
    for i in range(number_layers):
        if (i!=number_layers-1):
            c+="(= counter "+str(i)+") "
        else:
            c+="(= counter "+str(i)+")"
    f.write("\t\t\t(or "+c+")\n")
    f.write("\t\t)\n")
    
    c = ""
    
    for i in range(x):
        c+="x"+str(i)+"_prime "
        
    for i in range(x):
        c+="w"+str(i)+"_prime "
        
    for i in range(x):
        if (i!=x-1):
            c+="b"+str(i)+"_prime "
        else:
            c+="b"+str(i)+"_prime"
        
    
    f.write("\t\t(inv counter_prime "+c+")\n")
    
    f.write("\t)\n")
    f.write(")\n")
    
def write_bad_states(f,x,number_layers):
    f.write("\n")
    f.write("(rule\n")
    f.write("\t(=>\n")
    f.write("\t\t(and\n")
    
    c = ""
    for i in range(x):
        c+="x"+str(i)+" "

    for i in range(x):
        c+="w"+str(i)+" "
    
    for i in range(x):
        if (i!=x-1):
            c+="b"+str(i)+" "
        else:
            c+="b"+str(i)

    f.write("\t\t\t(inv counter "+c+")\n")
    
    if (binary_classification):
        f.write("\t\t\t(not (>= x"+str(which_class)+" 0))\n")
    else:
        d = ""
        for i in range(x):
            if (i!=which_class):
                if (i<which_class):
                    if (i!=x-1):
                        d+="(> x"+str(which_class)+" x"+str(i)+") "
                    else:
                        d+="(> x"+str(which_class)+" x"+str(i)+")"
                else:
                    if (i!=x-1):
                        d+="(>= x"+str(which_class)+" x"+str(i)+") "
                    else:
                        d+="(>= x"+str(which_class)+" x"+str(i)+")"
                    
        f.write("\t\t\t(not (and "+d+"))\n")
    
    f.write("\t\t\t(>= counter "+str(number_layers)+")\n")
    f.write("\t\t)\n")
    f.write("\t\tfail\n")
    f.write("\t)\n")
    f.write(")\n")
    f.write("\n")
    f.write("(query fail)\n")

def main():
    file_lines = read_nnet(my_file)
    file_lines = polish_file_lines(file_lines)
    number_layers, number_inputs, number_outputs, maximum_layer_size = from_first_line(file_lines)
    NN_architecture = from_second_line(file_lines)
    W = get_W(file_lines,NN_architecture,maximum_layer_size)
    b = get_b(file_lines,NN_architecture,maximum_layer_size)
    
    if (len(original_sample)!=maximum_layer_size):
        print("ERROR: wrong number of inputs in original_sample variable")
        return
    
    

    
    f = open(translated_file,"w")

    write_decl(f,maximum_layer_size,number_layers)
    write_header(f,maximum_layer_size,number_layers,W,b)
    write_transition(f,maximum_layer_size,number_layers)
    write_bad_states(f,maximum_layer_size,number_layers)
    f.close()
    
    
if __name__=="__main__":
    main()

#Erez Rigevsky, 322214172, Allen Bronshtein, 206228751
import hashlib, base64, string
import cryptography
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding

#prints root of tree
def get_root():
    if '' in snodes.keys(): return '',snodes['']
    else: return None,trivial_hashes[256]

# flips the lsb of binary form string
def get_brother(str):
    if str[len(str)-1] == '1': return str[:-1] + '0'
    elif str[len(str)-1] == '0': return str[:-1] + '1'
    return str 

#proof of inclusion for sparse merkle tree
def proof_of_inclusion_s(b,l):
    root = get_root()
    l.append(root[1])
    if root[0] is None: # root is white -> all tree is white
        return l

    for i in range(1,257):
        current=b[:i]
        brother = get_brother(current)
        if brother in snodes.keys(): l.append(snodes[brother])
        else: l.append(trivial_hashes[256-i])
        if current not in snodes.keys(): #current node is white
            break
    return l

#checks if proof is valid . return 1 if true , else returns 0
def proof_check(branch,b,p):
    hash_v = ''
    root_v = p[0]
    p = p[1:]
    if len(p) == 0:
        return True
    if (branch in snodes.keys() and b=='0') or (branch not in snodes.keys() and b=='1'): return False
    if b == '1':
        if len(p)!=256: 
            return False
        for i in range(0,257):
            if i == 256: # reached root
                if root_v == hash_v: 
                    return True
                return False
            data,value,brother_v = '',snodes[branch[:256-i]],p[255-i]
            if branch[255-i]=='0': data = value + brother_v
            else: data = brother_v + value
            hash_v = hashlib.sha256(data.encode('utf-8')).hexdigest()
    elif b == '0':
        level = len(p)
        hash_v = trivial_hashes[256-level]
        for i in range(0,level):
            data,brother_v = '',p[level-1-i]
            if branch[level-1-i]=='0': data = hash_v + brother_v
            else: data = brother_v + hash_v
            hash_v = hashlib.sha256(data.encode('utf-8')).hexdigest()
        if hash_v == root_v: 
            return True
        return False


            




# creates the trivial hashes for sparse merkle tree
def create_thashes():
    hashes = ['0']
    for i in range(0,256):
        curr = hashes[i]+hashes[i]
        hashes.append(hashlib.sha256(curr.encode('utf-8')).hexdigest())
    return hashes

#changes value of leaf from 0 to 1
def change_leaf(b):
    for i in range(0,257):
        key,value = b,'1'
        if i != 0:
            key = b[:-i]
            left,right = trivial_hashes[i-1],trivial_hashes[i-1]
            if b[:-i]+'0' in snodes.keys():# left son
                left = snodes[b[:-i]+'0']
            if b[:-i]+'1' in snodes.keys():# right son
                right = snodes[b[:-i]+'1']
            value = hashlib.sha256((left+right).encode()).hexdigest()
        snodes[key] = value

# defines Node in the merkle tree
class Node:
    def __init__(self, value):
        self.left = None
        self.right = None
        self.parent = None
        # self.value = value
        if value != "":
            self.hashValue = hashlib.sha256(value.encode('utf-8')).hexdigest()

# global variables
nodes = []  # all the nodes in the merkle tree
leaves_list = []  # holds all the leaves
root = None  # hold the root of the merkle tree
num_of_leaves = 0  # number of leaves

snodes = {} #nodes of sparse merkle tree
trivial_hashes = create_thashes() #list of trivial hashes of sparse merkle tree



# the function prints the tree for testing
def print_tree(node):
    if node is None:
        return
    if node.left is None and node.right is None:
        print(
            node.hashValue + ": left son -> None , right son -> None")
    elif node.left is not None and node.right is None:
        print(
            node.hashValue + ": left son -> " + node.left.hashValue + ", right son -> None")
    elif node.left is None and node.right is not None:
        print(
            node.hashValue + ": left son -> None" + ", right son -> " + node.right.hashValue)
    else:
        print(
            node.hashValue + ": left son -> " + node.left.hashValue + ", right son -> " + node.right.hashValue)
    print_tree(node.left)
    print_tree(node.right)


# the function reconstructs the tree from the leaves until the root by recursion
def reconstruct_tree(list):
    global root
    length = len(list)
    # stop condition for the recursion
    if length == 1:
        root = list[0]  # define the root
        return
    last_node = ""  # the last node in case of un-even number of leaves
    new_list = []
    if length % 2 == 1:
        last_node = list[length - 1]
        length = length - 1

    # go over the nodes list and for each 2 serial nodes create there father and add him to a new list
    for i in range(0, length, 2):
        node1 = list[i]
        node2 = list[i + 1]
        father = Node(node1.hashValue + node2.hashValue)
        father.left = node1
        father.right = node2
        node1.parent = father
        node2.parent = father
        new_list.append(father)
    if last_node != "":
        new_list.append(last_node)  # add last son to the new list
    reconstruct_tree(new_list)  # recursion


# the function adds a leaf to the merkle tree
def add_leaf(value):
    global nodes
    global leaves_list
    global num_of_leaves
    leaf = Node(value)  # create leaf Node from value
    # add new leaf to data structures
    nodes.append(leaf)
    leaves_list.append(leaf)
    num_of_leaves = num_of_leaves + 1
    reconstruct_tree(leaves_list)  # recreate the tree


# the function creates proof of inclusion
def proof_of_inclusion(leaf):
    hash_list = []
    node = leaf
    while node != root:
        # node is left son
        if node == node.parent.left:
            hash_list.append("1" + node.parent.right.hashValue)
        else:
            # node is right son
            hash_list.append("0" + node.parent.left.hashValue)
        node = node.parent
    return hash_list


# main function
if __name__ == '__main__':
    while 1:
        input_from_user = input()
        split = input_from_user.split(' ')
        command = split[0]
        params = []
        # simple checks
        try:
            command_num = int(command)
            if command_num < 0 or command_num > 11:
                print("")
                continue
        except Exception:
            print("")
            continue
        if len(split) > 1:
            params = split[1:]

        # execute command
        if command == '0':
            break
        if command == '1':
            if params[0] == '' or len(params) > 1:
                print("")
                continue
            add_leaf(params[0])
            continue
        if command == '2':
            if len(params) > 0:
                print("")
                continue
            if root is None:
                print("")
                continue
            else:
                print(root.hashValue)
                continue
        if command == '3':
            if params[0] == '' or not params[0].isnumeric() or int(params[0]) < 0 or int(
                    params[0]) >= num_of_leaves or root is None or len(params) > 1:
                print("")
                continue
            hash_list = proof_of_inclusion(leaves_list[int(params[0])])
            to_print = root.hashValue
            for node in hash_list:
                to_print += " " + node
            print(to_print)
            continue
        if command == '4':
            if len(params) < 1:
                print("")
                continue
            data = params[0]
            tree_root = params[1]
            hash_data = hashlib.sha256(data.encode()).hexdigest()
            hash_value = ""
            for i in range(2, len(params)):
                brother = params[i][1:]
                if params[i][0] == '1':
                    hash_value = hash_data + brother
                else:
                    hash_value = brother + hash_data
                hash_data = hashlib.sha256(hash_value.encode()).hexdigest()
            print(hash_data == tree_root)
            continue
        if command == '5':
            if len(params) > 1:
                print("")
                continue
            try:
                private_key = rsa.generate_private_key(public_exponent=65537, key_size=2048, backend=default_backend())
                pem = private_key.private_bytes(
                    encoding=serialization.Encoding.PEM,
                    format=serialization.PrivateFormat.TraditionalOpenSSL,
                    encryption_algorithm=serialization.NoEncryption()
                )
                print(pem.decode())
                public_key = private_key.public_key()
                pem = public_key.public_bytes(
                    encoding=serialization.Encoding.PEM,
                    format=serialization.PublicFormat.SubjectPublicKeyInfo
                )
                print(pem.decode())
            except Exception:
                print("")
                continue
        if command == '6':
            if root is None:
                while input() != "-----END RSA PRIVATE KEY-----":
                    input()
                print("")
                continue
            input1 = ""
            input_from_user = input_from_user[2:]
            input_from_user += "\n"
            while input1 != "-----END RSA PRIVATE KEY-----":
                input1 = input()
                if input1 == "":
                    continue
                input_from_user += input1 + "\n"
            try:
                bytes_key = input_from_user.encode()
                signature_key = serialization.load_pem_private_key(bytes_key, password=None, backend=default_backend())
                to_sign = root.hashValue.encode()
                signature = signature_key.sign(
                    to_sign,
                    padding.PSS(
                        mgf=padding.MGF1(hashes.SHA256()),
                        salt_length=padding.PSS.MAX_LENGTH
                    ),
                    hashes.SHA256()
                )
                print(base64.b64encode(signature).decode())
                continue
            except Exception:
                print("")
                continue
        if command == '7':
            input1 = ""
            public_key = input_from_user[2:] + '\n'
            while input1 != "-----END PUBLIC KEY-----":
                input1 = input()
                if input1 == "":
                    continue
                public_key += input1 + "\n"
            input1 = input()
            while input1 == "":
                input1 = input()
            input1 = input1.split(' ')
            signature = input1[0]
            message = input1[1]

            try:
                public_key = public_key.encode()
                public_key = serialization.load_pem_public_key(public_key)
                signature = base64.b64decode(signature)
                verify = public_key.verify(
                    signature,
                    message.encode(),
                    padding.PSS(
                        mgf=padding.MGF1(hashes.SHA256()),
                        salt_length=padding.PSS.MAX_LENGTH
                    ),
                    hashes.SHA256()
                )
                print('True')
            except cryptography.exceptions.InvalidSignature as e:
                print('False')
            except Exception:
                print("")
                continue
        if command == '8':
            # no params given
            try:
                digest = params[0]
            except Exception:
                continue
            # bad digest given
            if len(digest)!=64 or not all(c in string.hexdigits for c in digest):
                continue
            b = bin(int(hex(int(digest, 16)), 16))[2:].zfill(256)
            change_leaf(b)
        if command == '9':
            root = get_root()
            print(root[1])
        if command == '10':
            # no params given
            try:
                digest = params[0]
            except Exception:
                continue
            # bad digest given
            if len(digest)!=64 or not all(c in string.hexdigits for c in digest):
                continue
            b = bin(int(hex(int(digest, 16)), 16))[2:].zfill(256)
            l = proof_of_inclusion_s(b,l=[])
            msg, size = '',len(l)
            msg = msg + l[0] + " "
            for i in range(1,size):
                msg = msg + l[size - i] + " "
            msg = msg[:-1]
            print(msg)
            # f = open('10.txt','w') #<--- Erase when done testing
            # f.write(msg)
            # f.close() #<--- Erase when done testing
            
        if command == '11':
            # no params given
            try:
                # f = open('11.txt','r')#<--- Erase when done testing
                # _in = f.read()
                # f.close()
                # params = _in.split(' ')[1:]#<--- Erase when done testing
                digest = params[0]
                b = params[1]
                p = params[2] 
            except Exception:
                continue
            # bad digest given
            if len(digest)!=64 or not all(c in string.hexdigits for c in digest):
                continue
            # bad bit given
            if b != '0' and b!= '1':
                continue
            size = len(params)
            p = []
            for i in range(2,size):
                p.append(params[i])
            stop = False
            for h in p:
                if (len(h) != 64 and h != '0' and h != '1') or not all(c in string.hexdigits for c in h):
                    stop = True
            if stop:
                continue
            branch = bin(int(hex(int(digest, 16)), 16))[2:].zfill(256)
            root = p[0]
            p = p[1:]
            p.reverse()
            p.insert(0,root)
            v = proof_check(branch,b,p)
            print(v)            
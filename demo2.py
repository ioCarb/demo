import os
import json

from zokrates_pycrypto.eddsa import PrivateKey, PublicKey
from zokrates_pycrypto.field import FQ
from zokrates_pycrypto.utils import write_signature_for_zokrates_cli, to_bytes


pebble_path = os.path.join(os.pardir, 'pebble-simulator/pebble.dat')

if __name__ == "__main__":
    with open(pebble_path, 'rb') as file:
        pebble_data = json.load(file)
        timestamp = pebble_data['message']['timestamp']
    # Without hashing and he integer 
    # ist also readable in the in the 'zokrates_inputs.txt' 
    # file but wont verify in Remix.
    integer = int(timestamp)
    msg = to_bytes(integer)
    print(msg)

    # Seeded for debug purpose
    key = FQ(1997011358982923168928344992199991480689546837621580239342656433234255379025)
    sk = PrivateKey(key)
    sig = sk.sign(msg)
    #print(sig)

    pk = PublicKey.from_private(sk)
    #print(pk.p)


    is_verified = pk.verify(sig, msg)
    #print(is_verified)

    path = 'zokrates_inputs.txt'
    write_signature_for_zokrates_cli(pk, sig, msg, path)
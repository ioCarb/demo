# Welcome to the demo

We will implement a reading on the [pebble-simulator](https://github.com/iotexproject/pebble-simulator) and to sign that reading with [PyCrypto](https://github.com/Zokrates/pycrypto). This signed reading will then be verified in [ZoKrates](https://github.com/ZK-Plus/ZoKrates). ZoKrates will provide us with a verifier contract that we will deploy on the [IoTeX Network Testnet](https://docs.iotex.io/the-iotex-stack/iotx-faucets/testnet-tokens) via [Remix IDE](https://remix.ethereum.org) and a proof that we will provide on-chain to show the verification of the readings signature. 

## MetaMask

Install a browser plugin of [MetaMask](https://metamask.io/). Follow the instructions that apply for you, new private key, recover or just add a new account.

## IoTeX

Register via github and caim daily IOTX on your [developer profile](https://developers.iotex.io/user/profile).


## Pebble Simulator 

Set Number of Data Points to 1 and config privkey to: 46a44b42846312eee2f16708c1c508de917ac42703cbd0531281cafb5857a51 (not necessary now, but later perhaps).


<!--Public Key: x=14897476871502190904409029696666322856887678969656209656241038339251270171395, y=16668832459046858928951622951481252834155254151733002984053501254009901876174-->


```
========>> PEBBLE SIMULATOR <<========


 1.  Config Sensors

 2.  Set Number of Data Points (Current: 2)

 3.  Generate Simulated Data

 4.  Publish to IoTT Portal

 5.  Device Registration

 6.  Set Device IMEI (Current: 103381234567406)

 7.  Config device privkey (Current: 46a44b42846312eee2f16708c1c508de917ac42703cbd0531281cafb5857a51)

 8.  Networks (Current: testnet)

 9.  Exit

Select:
```
Set Number of Data Points to 2 and Generate Simulated Data. This will create a **pebble.dat** file containing the data in the root folder of the pebble-simulator.

## PyCrypto

Create a new file in the root folder of pyCrypto **two_gmp_coordinates.py**.

```
import hashlib
import os
import json

from zokrates_pycrypto.eddsa import PrivateKey, PublicKey
from zokrates_pycrypto.field import FQ
from zokrates_pycrypto.utils import write_signature_for_zokrates_cli, to_bytes

pebble_path = os.path.join(os.pardir, 'pebble-simulator/pebble.dat')

def byte_repr(i):
    result = i.to_bytes((i.bit_length() + 7) // 8, 'big')
    return result


def convert_lat(lat):
    lat_unsigned = int((lat + 90) * 10**7)  #Shifting the range from -90...90 to 0...180 and move the decimal places
    return lat_unsigned

def convert_lon(lon):
    lon_unsigned = int((lon + 180) * 10**7) #Shifting the range from -180...180 to 0...360 and move the decimal places
    
    return lon_unsigned


if __name__ == "__main__":

    print("=================== Original Data ===================")
    json_objects = []

    with open(pebble_path, 'r') as file:
        for row in file:
            json_objekt = json.loads(row)
            json_objects.append(json_objekt)

    for i, object in enumerate(json_objects):
        if i == 0:
            latitude1 = object['message']['latitude']
            longitude1 = object['message']['longitude']
            print(f"Latitude 1: {latitude1}, Longitude 1: {longitude1}")
        elif i == 1:
            latitude2 = object['message']['latitude']
            longitude2 = object['message']['longitude']
            print(f"Latitude 2: {latitude2}, Longitude 2: {longitude2}\n")

    lat1 = convert_lat(latitude1)
    long1 = convert_lon(longitude1)
    lat2 = convert_lat(latitude2)
    long2 = convert_lon(longitude2)

    print("Shifting the latitude range from -90...90 to 0...180 and move the decimal places")
    print("Shifting the longitude range from -180...180 to 0...360 and move the decimal places\n")

    print("=========== converted to unsigned integers ==========")
    print(f"Latitude 1: {lat1}, Longitude 1: {long1}")
    print(f"Latitude 2: {lat2}, Longitude 2: {long2}\n")

    #placeholder=byte_repr(11111111)
    blat1 = byte_repr(lat1)
    blong1 = byte_repr(long1)
    blat2 = byte_repr(lat2)
    blong2 = byte_repr(long2)

    print("================= converted to bytes ================")
    #print("Placeholder:", placeholder)
    print(f"Latitude 1: {blat1}, Longitude 1: {blong1}")
    print(f"Latitude 2: {blat2}, Longitude 2: {blong2}\n")

    msg = to_bytes(blat1, blat1, blat1, blat1, blong1, blong1, blong1, blong1, blat2, blat2, blat2, blat2, blong2, blong2, blong2, blong2)

    print("============== message that gets signed =============")
    print(msg)

    # Seeded for debug purpose
    key = FQ(1997011358982923168928344992199991480689546837621580239342656433234255379025)
    sk = PrivateKey(key)
    sig = sk.sign(msg)
    #print(sig)

    pk = PublicKey.from_private(sk)
    #print(pk.p)

    #is_verified = pk.verify(sig, msg)
    #print(is_verified)

    path = 'zokrates_inputs.txt'
    write_signature_for_zokrates_cli(pk, sig, msg, path)
```
Run **python two_gps_cordinates.py** and the script will load the JSON in the pebble.dat, identify the GPS cordinates, sign them and write a zokrates_inputs.txt containing the witness inputs for ZoKrates.

# Remix

Open [Remix online IDE](https://remix.ethereum.org) and install ZoKrates with the plugin manager. Klick on **deploy and run transactions** and choose WalletConection in the Environment. 

If your wallet does not connect to the Remix IDE, click on the plug symbol right from Environment to be forwarded to **chainlist** where you search for IoTeX and include testnets. Connect with your wallet and return to **Remix online IDE** which should now allow you to connect to your wallet. 

## File Explorer

Switch to the file explorer tab on the left side and add a new file **calculations_and_verification.zok**. 

```
from "ecc/babyjubjubParams" import BabyJubJubParams;
import "signatures/verifyEddsa.zok" as verifyEddsa;
import "ecc/babyjubjubParams.zok" as context;

def main(private field[2] R, private field S, field[2] A, u32[8] M0, u32[8] M1) -> u32 {
    BabyJubJubParams context = context();
	assert(verifyEddsa(R, S, A, M0, M1, context));
    
    u32 latitude1 = M0[0];
    u32 longitude1 = M0[4];
    u32 latitude2 = M1[0];
    u32 longitude2 = M1[4];

    u32 diff_latitude = latitude2 - latitude1;
    u32 diff_longitude = longitude2 - longitude1;

    u32 km = diff_latitude + diff_longitude;

    return km;
}

```

## ZoKrates

Switch to the ZoKrates tab on the left side and choose GM17 as the prooving scheme. Then compile. Then compute and enter the inputs generated by the **zokrates_inputs.txt**. Run the setup. Generate the proof and don't forget to click to copy, the format in the proof.json is not identical. Save the copied proof in a text file. Export to create the **verifier.sol**.

## Solidity compiler

Switch to the Solidity compiler to the left and compile the **verifier.sol**.

## Deploy and run transactions

Switch to the Deploy and run transactions to the left and choose the **Verifier - verifier.sol** in Contract and Deploy. Confirm the transaction in MetaMask two times.

Open the verifier contract in **Deployed/Unpinned Contracts** and pin the contract.

Now copy the proof you saved in a text file directly into the verifyTx field after that open the menu by clicking on the arrow and click on send/call.

In the terminal you then can open the call log and see: 

```
decoded output
{
	"0": "bool: r true"
}
```


You can now look the contract up on [iotexcan](https://testnet.iotexscan.io). 

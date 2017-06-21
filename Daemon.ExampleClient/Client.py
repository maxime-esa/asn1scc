#!/usr/bin/env python
import requests

def run(uri):
    print("asn1scc Daemon Test Client")
    print("asn1scc Daemon version:", requests.get(uri + "version").content)

    data = {
        'AsnFiles': [
                {
                    'Name': 'Test.asn',
                    'Contents': 'Example DEFINITIONS ::= BEGIN MyInt ::= INTEGER(0 .. 10) END'
                }
        ], 
        'AcnFiles': []
    }

    print("Requesting AST XML for contents: ", data['AsnFiles'][0]['Contents'])
    print("AST:")
    print(requests.post(uri + "ast", json = data).content)


if __name__ == "__main__":
    import sys
    uri = sys.argv[1] if len(sys.argv) > 1 else "http://localhost:9749/"
    run(uri)

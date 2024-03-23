from glob import glob
import base64
import json


for file in glob('metadata*'):
    try:
        print(f"Decoding {file}...")

        with open(file, "r") as f:
            data = f.read()
            data_parse = data.replace("data:application/json;base64,", "")
            json_data = base64.b64decode(data_parse)
            json_data = json.loads(json_data)
            image_string = json_data["image"]
            svg_data = image_string.replace("data:image/svg+xml;base64,", "")
            svg_parse = base64.b64decode(svg_data)

        with open(file + ".svg", "w") as f:
            f.write(svg_parse.decode('utf-8'))

    except UnicodeDecodeError as e:
        print(e)
        continue



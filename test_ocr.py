
import sys
from PIL import Image
import numpy as np

# --- Helper classes from translator.py ---
class Word:
    def __init__(self, text, x, y, w, h):
        self.text = text
        self.x = x
        self.y = y
        self.w = w
        self.h = h

class PaddleOCR_Wrapper:
    def __init__(self, lang="en"):
        from paddleocr import PaddleOCR
        self.ocr = PaddleOCR(use_angle_cls=True, lang=lang)

    def recognize(self, img):
        # Ensure image is in RGB format (numpy array)
        results = self.ocr.ocr(np.array(img.convert("RGB")), cls=True)
        words = []
        if results is None: return words
        for line in results:
            if line is None: continue
            for word_info in line:
                # word_info: [box, (text, confidence)]
                text = word_info[1][0]
                words.append(Word(text, 0, 0, 0, 0))
        return words

# --- Testing ---
img_path = r"C:\Users\Yaggdrasil\AppData\Local\Packages\MicrosoftWindows.Client.Core_cw5n1h2txyewy\TempState\ScreenClip\{88C60BCE-9D9F-41C8-B96B-CFD9CB689D16}.png"

try:
    img = Image.open(img_path)
    print(f"Image opened: {img.size}, {img.mode}")
    
    ocr = PaddleOCR_Wrapper()
    words = ocr.recognize(img)
    print(f"Recognized {len(words)} words:")
    for w in words:
        print(f"  '{w.text}'")
except Exception as e:
    print(f"Error: {e}")

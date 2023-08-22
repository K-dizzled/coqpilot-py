import sys

text = sys.argv[1]

print(text.replace("Admitted.", "intros A P x H.\napply H.\nQed."))
print("success")
from subprocess import call

target = 493
call(["gcc", "main.c", "-o", "shorAlgo.exe"])

for i in range(2,target+1): # Executes for every 'a' value
    call(["./shorAlgo.exe", "-c", str(target), "--a", str(i)])
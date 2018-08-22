all:a.out bot.out

a.out:MyBot.c
	gcc MyBot.c

bot.out: MyBotCeuC.c
	gcc MyBotCeuC.c -o bot.out

MyBotCeuC.c: types.h threads.h MyBotCeu.c main.c 
	ceu --env \
	--env-types=types.h \
	--env-threads=threads.h \
	--env-ceu=MyBotCeu.c \
	--env-main=main.c \
	--env-output=MyBotCeuC.c


MyBotCeu.c: MyBot.ceu
	ceu --ceu --ceu-input=MyBot.ceu --ceu-output=MyBotCeu.c

clean:
	rm a.out bot.out MyBotCeuC.c MyBotCeu.c

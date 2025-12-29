This is a [Claude Opus 4.5](https://en.wikipedia.org/wiki/Claude_\(language_model\))-generated [Lean](https://en.wikipedia.org/wiki/Lean_\(proof_assistant\)) proof of [Morley's Trisector Theorem](https://en.wikipedia.org/wiki/Morley%27s_trisector_theorem).

# Why?

Right now there's a thing going on on Twitter where someone claims to have solved [Navier-Stokes](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_equations) using Claude. I consider this . . . not technically impossible, I suppose, but *very very unlikely*. But this got me thinking; if AI is not yet good enough for cutting-edge research, is it at least good enough to solidify not-cutting-edge research? Can it generate valid formal computer-verifiable mathematics proofs given a believed-correct-but-not-formal-computer-verifiable-mathematics-proof?

And can it do so *mostly* on its own, but when handled by a non-mathematician who understands working with AI pretty well? See, I'm not a mathematician, I'm a programmer. But I have been working with AI. So can I use AI to make something that *I* don't understand, and that has not been done yet, but that is still potentially useful? Also, Lean is definitely *kinda programmer-language-y*, so I thought that maybe my programming skills would come in useful just in terms of pointing Claude towards the right thing to do.

A lot of people are asking Claude et al to generate this stuff in a vacuum, and I think that's just a terrible idea. Real mathematicians don't do that! Check out [this totally cool video where Terence Tao writes a Lean proof](https://www.youtube.com/watch?v=cyyR7j2ChCI); you'll note he has realtime feedback from his IDE constantly telling him what is or isn't working.  Part of the reason I wanted to use Lean is because it can provide this feedback, and if I'm using Claude Code locally, I can just point it at Lean commandline tools and say "use this to check your work". I'm not going to claim that's perfect but it's a damn sight better than expecting it to generate an entire formal mathematical proof out of the ether that works on the first shot. Terence Tao can't do that, and if Terence Tao can't do it, I'm not going to damn Claude for not being able to do it.

I asked someone on a Discord if they could come up with a few not-formally-verified-but-not-too-difficult mathematics papers that I could feed into Claude, using my above-average AI skills and nearly-nonexistent math skills, and see if I could get valid Lean proofs out; also I wanted to know if there was a good database of existing Lean proofs to point Claude towards, as I've found Claude gains a lot from having reference code to work from. They pointed me to the [Lean Wiedijk 100 Theorems page](https://leanprover-community.github.io/100.html) for the latter and said they were just about to go to bed but they'd think about the former.

I didn't want to wait, and I realized there was a Theorems Not Yet In Lean link, so I browsed a few of those and decided to give it a try.

# Why Morley's?

First, the proof to Morley's is not trivial or simplistic. I know this because nobody's done it in Lean yet. It's not going to be a one-liner, it's going to be more complicated than that. Possibly far more complicated!

Nevertheless, the Wikipedia page lists multiple proofs, one of which is short enough to fit on that very same Wikipedia page. This fits into a nice space between a Lean one-liner and "are you seriously trying to formalize Fermat's Last Theorem, what the fuck"; this is something that's chunky and would be a significant amount of work for a human, and this felt like a reasonable test of "can AI be used to do things that are actually sorta significant".

(I don't remember the page that gave an estimate, but it estimated "one to two weeks of work for a grad student", and this roughly parallels the hilariously incorrect human-scale estimates Claude kept feeding me.)

This is getting a bit ahead of the timeline, but Morley's actually *does* have existing computer-verifiable proofs . . . just none in Lean. I decided that I was OK with this - this still gave me a lower bound on whether AI can do this sort of thing ("can it convert proofs from one language to another?") and if the answer turned out to be "no, it can't even do that", then fine, it probably can't make up new proofs for things that haven't been computer-verified, I guess that answers the question.

In addition, one of the Morley's proofs made extensive use of affine transformations. My specialty is computer rendering and I am very familiar with affine transformations, admittedly in a "convince a GPU to render a goblin stabbing a dude" sense and not a "mathematical proof" sense, but still, I figured this might come in handy.

# What was the process?

Claude knows a lot, even in obscure subjects, and is good at thinking, but I generally find it's not great at repeatedly thinking about obscure subjects, you have to give it a foundation to start on. I used Claude web interface's Research feature to generate [a Lean 4 reference](https://github.com/zorbathut/morleys/blob/dev/ref/lean.md), and then used a separate Claude Research to generate [a reference on Morley's](https://github.com/zorbathut/morleys/blob/dev/ref/morleys.md). In retrospect I then forgot to actually make a CLAUDE.md - I did point it to these a few times but it's possible I could have done better here. This is the point where I discovered the "existing computer-verifiable proofs" thing, so I went and downloaded the proofs and tossed them into [a sub-directory of ref](https://github.com/zorbathut/morleys/tree/dev/ref/morley_references).

(Actually I told Claude to write a script to download them, which it did. It then tried to execute the script, which it couldn't because of its sandbox, and then spent like five minutes trying unsuccessfully to get around its own sandbox. I sighed and grabbed the script and ran it manually locally, which had been my plan the entire time.)

I skimmed all of these just to make sure they weren't obviously insane, but I *don't know Lean* so this was basically "did you get distracted and spend half the time talking about clams or something", just in case. (It didn't.)

From there, it was Claude Code time. I told it to work up a detailed plan (it asked me questions like "which approach should I use"; I pretty much always said something like "use your best judgement", and was somewhat relieved when it independently decided to do the affine-transformation proof) and then I had it get started.

&nbsp;

And then it took a while.

# Did it work?

Kinda.

The core problem I ran into is simply that Claude's context is not long enough for something of this complexity and depth. I would have situations where it would spend quite literally *its entire context* on analyzing a problem and conclude it had a solution but didn't have enough context to write it. I'd compress the context, keeping the solution in context, but then it would need to go do most of the research again to understand it *properly enough* to feel like it could implement it. Nevertheless, it kept making steady progress. I had it commit after every significant chunk of work, and you can see the full commit history, so you can see what it did.

One of the issues the Navier-Stokes guy is running into is that his demonstrated code is full of `sorry`s and `axiom`s. If you're not familiar with Lean (hello, me, three days ago) these are basically telling the Lean compiler that you acknowledge you don't have a solution for it but maybe just take it on faith for now. It's a useful thing for intermediate work - Terence Tao's video linked above is *full* of `sorry`s - but then you gotta fix those, you can't just say "proof: it came to me in a dream!" and get away with it in the long run. Thankfully the Lean compiler is very vocal about `sorry`s, and Claude made no attempt to hide it, so whenever I noticed a commit that included a `sorry`, I'd let it commit, then tell it go fix the `sorry`, and it (reliably!) would.

Note that part of the reason I was so proactive on this is that Claude can be very lazy if it thinks it can get away with it. If you just let Claude run rampant, it'll add stub functions, then add more stub functions, then at some point it's not actually doing work, just saying "well, my controller seems to think this behavior is fine, I'm just gonna stick with it". Claude writes code that's slightly worse than existing code and you can see how this can quickly spiral out of control. I did not want it to get into that loop and so I headed it off at every opportunity.

Near the end, it ran into a tangle it couldn't solve, and made an `axiom`. As near as I can tell, the intent for `axiom` is that it's not an unfinished bit in the proof, it's someone straight-up saying "okay, assuming that X is true . . ." Which can be an interesting thing to include in a mathematical proof, but isn't what I was going for here. So I asked it to fix the axiom.

And that ended up being about a third of the total work.

----

So, okay, back up a second. I don't know what the "right" way to write a Lean proof is. I don't think Claude knows that either. Maybe there isn't one? But as a programmer, I'm thinking about this in terms of "top-down" or "bottom-up", the first where you write the fundamental theorem you're trying to prove (and you prove it with a puddle of `sorry`s or, in the programming world, stub functions) and then you go and clean all those up until you're done with your thing. The latter where you write the fundamental foundation that you need, and when you do that you build the second floor, and so forth, until you put the pinnacle on top and *now* your thing is done.

Anyway, Claude went with bottom-up, which presented an issue when it got to the pinnacle and discovered that the pinnacle didn't fit. That's why it built the axiom; it basically said "connecting the foundation I made to the actual solution is too hard! so I'm not gonna do it, bye now."

I went through *several* full contexts trying to get it to solve the issue. The problem seems to have been that rotations aren't commutative - rotating A then B is not the same as rotating B then A - and it had built the foundation with the wrong rotation order. I kept asking it for a solution, it kept running in circles, running out of context, and then starting over after a context compact.

I've found that Claude is, in general, somewhat resistant to refactoring. It really *really* wants to keep backwards compatibility with everything. On my own projects I keep having to tell it to get rid of backwards compatibility stubs and just make the refactor changes; the only thing that depends on my code *is my code*, you can see the whole thing, just remove the stubs for fuck's sake. This is conjecture, but I think that's what was going on here. It didn't want to write an entire new codebase with a different rotation order because that's duplicate code, and it didn't want to change the existing code because that would break "backwards compatibility" (with a codebase that didn't actually exist), so it was looking for a simple clean way to connect the two without doing either of those, and one simply didn't exist. Or at least Claude wasn't smart enough to find it, and I certainly aren't.

Eventually I broke the logjam by just flat-out ordering it to change the rotation order. [It did](https://github.com/zorbathut/morleys/commit/0d2c140f8eb718287235e9c59a1737c5e80fe447), and then the rest of the work came pretty quickly from there.

(This was the only time my experience with affine transformations actually came in handy, and was the only time in the initial proof that I actually told it what to do, besides an eternal stream of "keep working, commit, fix the sorry, compact, keep working".)

----

It's worth noting that this entire time, it seemed to be *heavily* consulting the Isabella proof. This is not a proof generated in a vacuum, this is a port of the Isabella proof. And that's the second reason I'm saying "kinda" to "did it work". It was a pain; it wasn't really automatable because I had to intervene to kick it out of a loop; and even as much as it did, it only did because it had a reference proof.

Perhaps Morley's was too hard and it would have had a better time with something easier. *Are* there easier proofs that haven't been computer-verified, where computer-verifying them would be useful? If you know of one, drop an issue on Github! Perhaps I will try it! But I don't know of one offhand and the person on Discord hasn't gotten back to me (I also haven't pestered them, and, I mean, it is the holidays.)

I also don't know if Morley's is notably easy or hard for Claude. I know I always hated computational geometry. Perhaps Claude does too (mood), and if I'd picked something with less geometry, Claude would have just steamrolled it. Or perhaps it's the opposite and I happened to pick something Claude is uncommonly good at. I have no evidence either way, or any evidence that this is even out of the ordinary, but it's a possibility.

# Is it going to be added to Mathlib and to the page on missing proofs?

Maybe?

So, first, I haven't actually finished the process of making sure this is a valid proof. The Lean page has this nice page on [Did you prove it?](https://leanprover-community.github.io/did_you_prove_it.html), which was *very* helpful. Most of the things listed here I can confidently check off; there are no `sorry`s, there are no `axiom`s, the main file is indeed being compiled. It is definitely proving the thing defined by [the main theorem](https://github.com/zorbathut/morleys/blob/dev/Morleys/Morley.lean#L283)!

Is that thing Morley's?

Well . . . I think so. Again, I'm not a mathematician, but I do have basic knowledge and can read computer code. I look over the theorem definition and say "yeah, that's not obviously wrong, at least", I didn't have it write three thousand lines of Lean just to prove 1=1. However, I do need to run this past an actual mathematician. Perhaps there's some deep flaw in the fundamental theorem definition that makes this entirely invalid. I dunno.

Assuming it's valid, though . . .

. . . I don't actually know if Mathlib wants it.

From what I understand, the Mathlib theorem list isn't *really* intended as a comprehensive list of proofs of that list without any other goals, it's intended as a Lean integration test and demo code. And I suspect this is, shall we say, not exactly the cleanest Lean code ever written. I did skim over the code at the end and see one thing that triggered my bad-code-spider-sense, [and had Claude fix it](https://github.com/zorbathut/morleys/commit/b0a3e4b4c8143128508d0c2e298baa9448871a7e) (and then sighed and had Claude [remove the backwards-compatibility stubs](https://github.com/zorbathut/morleys/commit/588cd98dc8c0059d72174574d5459ed8c927d43f)), and I also had it do final comment and library-usage cleanup passes. But if I, a person who doesn't know Lean, can still find a pretty awful bit of Lean code, then this suggests there's probably a lot more awful stuff in there that I'm simply not capable of seeing. And I frankly have no idea if the comments are even coherent, let alone correct.

Maybe they don't care! Or maybe, now that this first step is done, the community will say "oh no problem, Claude did all the hard work, cleanup is simple, we'll take it from here, thanks!"

Or maybe they'll say "fucking hell get this garbage out of here we'd rather have it not solved at all than solved with this atrocity that pollutes the very name of math I curse your family and your descendents to the hundredth generation".

I admit I'll be a *little* disappointed if they're not interested, but not catastrophically so, because, I mean, I get it, I dunno if I'd want three thousand lines of possibly-unreadable code in my repos either. When I'm working with Claude on my stuff, I read it over and fix it, but I am explicitly *not* qualified to do so here, and if this is both terrible and hard to fix, then I too would absolutely reject this much code by some schmuck who doesn't know what they're doing, even if they insisted it worked.

Que sera sera.

# How much did it cost?

It's kind of hard to say.

I have the Claude Max plan, $100/mo for 5x normal usage. I started this on a new week (not intentionally, just conveniently) and when I finished, my meter read 17% of the total weekly usage. But I was also doing development on my own project at the time. I think I'd estimate something in the 12%-15% range for this proof specifically. This is also misleading, because I did it right after Christmas when Anthropic was offering double quotas, so . . . 24%-30% of a normal 5x weekly quota?

So if we try to amortize it out, this ends up being (4.5 weeks per month, $100/mo) about six bucks.

But I also have never actually hit my cap, so if we're calculating it in terms of how much I actaully use, probably about twenty bucks.

But then, *I have never hit my cap*, and I would be subscribed to Claude Max anyway, so, zero bucks?

Meanwhile, ccusage reports that this has been the equivalent of about $118 of API usage over the last few days. I'm not totally sure if ccusage is reliable. But if it is, that means around $94 spent on this if you were doing it via the API. (The subscription is obviously a *much* better deal.)

If you want to do this yourself, and you want to try it with the $20/mo Pro subscription, it'll probably take you about two weeks, because you'll hit your weekly cap before it's finished and have to wait another week.

# Why Claude?

* Claude is not always the absolute best, but it's always pretty close to the best, so I just stick with it, and usually it becomes the best again in a month or so without me having to fuck up my workflow every few weeks chasing thin shavings of optimal.

* Partially thanks to the above, I'm used to it.

* I've got friends working at Anthropic.

* I overall feel like Anthropic has the best chance of solving AI alignment before the shoggoth eats us all, and I would like to support that.

# blah blah environmental damage blah blah electricity use blah blah water use blah blah

Check your numbers and stop spreading misinformation, yo.

This whole process was something like a day and a half, but this includes sleeping and a lot of me not paying attention to the computer (we had a late Christmas, so I literally spent a lot of that time opening presents with the kids, watching How To Train Your Dragon with them, and just generally hanging out.) This was probably under twelve hours of computer time, but let's use that figure anyway. Individual AI servers use maybe 2kW of power, so assuming I used the entire server (which, again, I probably didn't), that's 24kWH. For comparison, that's roughly the energy used to bake two turkeys, drive twenty miles, *or* spend an hour in the shower.

Water usage is frankly even less relevant; again, assuming the above numbers are correct, and this is all coming from a less-water-efficient datacenter, it's around 12 gallons of water used on cooling. That *sounds* like a lot because we're used to fluid numbers when we're talking about personal consumption, and 12 gallons would be a lot of water to drink . . . but a single hamburger uses around 1000 gallons, and the aforementioned hour-of-shower would use around 120 gallons, and the *really big* mug of tea I'm drinking, right now, probably used something like [26 gallons of water](https://sustainablebrands.com/read/how-much-water-to-make-a-cup-of-tea-the-importance-of-product-water-footprinting-for-businesses) all put together. I'll let you do your own math on how much water I spend on feeding [the cat on my lap](https://photos.app.goo.gl/qD5z1NNPcZBdfSmh8).

(He says mrowp.)

AI power usage and water usage are a *tiny* fraction of humanity's total usage, and the people crying doom over this are fundamentally just getting scared about large numbers that they have no civilization-scale context for.

I am not worried about this subject.

# Wait, did you say "before the shoggoth eats us all"?

Haha.

Yeah.

Interesting times, eh?

# So, conclusion?

This was cool and I don't regret the time spent on it.

I suspect Claude is not yet at the point where it's reasonable to just aim a datacenter at a pile of unformalized mathematical proofs, say "have at it!", and walk away. On the other hand, a year ago this would have been unthinkable. A year from now we might well be able to have AI verifying proofs, in aggregate, *entirely unassisted*. Neat!

Meanwhile, someone who actually knows what they're doing would probably be *much* more effective. We are, for now, still in the world where a human/AI tag-team is a huge improvement over either working alone. Are you a math grad student? Do you want to write computer proof formalizations quickly? Give it a try on your own! I'm happy to assist, ping me on Discord, my username there is my username here.

(If you're Terence Tao, you probably know more than I do about this already.)

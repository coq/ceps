---
Title: Transitioning from X/Twitter to new social media platforms
Drivers: Théo Zimmermann (@Zimmi48)
---

## Summary

This RFC proposes to reform the management of the official social media channels of Coq in the context of the renaming to the Rocq Prover. In particular, it proposes to: search for additional volunteers to help manage them, and to revisit which social media platforms to be present on in the current context.

## Context and motivation

During the last four years, the Coq project's social media presence has been limited to the CoqLang account on Twitter (then X). This account was initially managed by three persons: Emilio Jesús Gallego Arias, Anton Trunov, and Théo Zimmermann. However, in the last two years, the account has been mostly managed by Emilio Jesús Gallego Arias alone (Anton Trunov is not active anymore in the Coq ecosystem, and Théo Zimmermann has stopped using X/Twitter).

Leaving the management of the account on the shoulders of a single person is not sustainable in the long term. If the project wants to maintain a social media presence, it needs to involve more people in the management of its social media account(s).

The CoqLang account uses the Coq-community logo instead of the Coq logo, because it is largely considered as a better visual identity for the Coq project. However, the CoqLang account is still the official account of the Coq project. In the context of the renaming of Coq to the Rocq Prover, we have to decide what to do with respect to our social media presence. If we keep the CoqLang account, we will have to rename it and to update its visual identity to use the new Rocq Prover logo.

With the change of ownership of X/Twitter and the associated changes in moderation policies, the general social media context is much different than it was four years ago when it was decided to create the CoqLang account. In particular, many academics have left X/Twitter and moved to alternative platforms such as Mastodon (or more recently Bluesky). More recently, many journalists have also started to leave X/Twitter. Beyond individual decisions, there are now media (such as [The Guardian][guardian] in the UK, [La Vanguardia][lavanguardia] in Spain, [NPR][npr] in the US, [Ouest France][ouestfrance] and [Mediapart][mediapart] in France) and academic institutions (e.g., [Aix-Marseille University][amu], [University of Strasbourg][unistra], [University of Luxembourg][unilux], [RWTH Aachen][rwth], [Utrecht University][uu], [York University][york]) that are officially leaving X/Twitter as well.

[guardian]: https://www.theguardian.com/media/2024/nov/13/why-the-guardian-is-no-longer-posting-on-x
[lavanguardia]: https://www.lavanguardia.com/vida/20241114/10105193/vanguardia-dejara-publicar-x-convertido-red-desinformacion.html
[npr]: https://www.npr.org/2023/04/12/1169269161/npr-leaves-twitter-government-funded-media-label
[ouestfrance]: https://www.lemonde.fr/pixels/article/2024/11/19/ouest-france-annonce-suspendre-ses-publications-sur-le-reseau-social-x_6403278_4408996.html
[mediapart]: https://www.mediapart.fr/journal/france/171224/contre-la-desinformation-mediapart-quitte-x
[amu]: https://www.univ-amu.fr/en/public/actualites/aix-marseille-universite-suspends-its-activity-x
[unistra]: https://www.unistra.fr/communiques-presse/detail-communique-de-presse-archive/22529-the-university-of-strasbourg-leaves-the-social-network-x-ex-twitter
[unilux]: https://www.uni.lu/en/news/university-suspends-its-x-twitter-account/
[rwth]: https://x.com/RWTH/status/1861320302124253564
[uu]: https://www.uu.nl/en/news/utrecht-university-quits-x
[york]: https://www.york.ac.uk/library/about/news/2024/ex-x/

<summary>The arguments given by these universities to justify their departure from X/Twitter vary quite a lot (from the lack of respect for the European code of good conduct and the proliferation of false information and conspiracy theories to the diminishing reach of X/Twitter compared to other platforms):

<details>

>By withdrawing from the European code of good practice against misinformation and
modifying its moderation rules, X has become a place where fake news, hateful, illicit or
violent content is propagated. This social network is no longer aligned with our mission of
transmitting knowledge and science, openness to others and tolerance.

>This decision has been motivated by the evolution of this network: lack of respect for the European code of good conduct, paid certification, proliferation of false information and conspiracy.

>The editorial and commercial evolution of X/Twitter in recent months has come to conflict with the University’s values of diversity, inclusion and social dialogue. The disbanding of the moderation team at X/Twitter and the fact that the social media platform pulled out from the European Union’s voluntary code to fight disinformation further informed this decision.

>Due to the promotion of anti-democratic, anti-scientific content and conspiracy theories on the platform X, RWTH Aachen University is going to discontinue its activities on it. The platform is not sufficiently addressing hate speech, hatred against minorities, conspiracy theories, and right-wing extremist opinions – in short, it is not doing enough to combat radicalization. We will continue to provide information on our other social media channels (Instagram, LinkedIn, YouTube, TikTok, Threads and Facebook).

>In recent years, UU's reach on X has decreased compared to other platforms, such as LinkedIn. In addition, we have seen how X, often more than other platforms, struggles with the rise of disinformation, fake accounts and online harassment.

>This is for a number of reasons: primarily it no longer works as an effective method of distributing information to our communities. 
</details>
</summary>

Also, six months after leaving X/Twitter, [NPR claims that the effect on their audience has been negligible](https://pluralistic.net/2023/10/14/freedom-of-reach/).

## Design

We have to decide what the social media presence of the Rocq Prover will be. The options are:

- No social media presence: leave X/Twitter and do not create accounts on other platforms. This is the only alternative that does not require calling for volunteers. In all other cases, we need to expand the social media team.
- Keep the CoqLang account on X/Twitter and rename it to Rocq Prover. Expand the team of people managing the account.
- Keep the CoqLang account on X/Twitter and create new accounts on other platforms. This requires expanding the team of people managing the accounts even more, as it seems unlikely that the same people will manage all the accounts (even in the case of one account automatically reposting from another, because we need to monitor replies and DMs).
- Leave X/Twitter and create new accounts on other platforms. This still requires finding volunteers to manage the new accounts.

The volunteers we find will depend on the platforms we target. We can have a predefined list of platforms to target, but we can also be open to suggestions from the community. Furthermore, we cannot create accounts on platforms for which we do not find volunteers.

I propose to target the following platforms: Mastodon, Bluesky, and LinkedIn. I also propose to be open to suggestions from the community, but to decide upfront to leave X/Twitter. Of course, an alternative would be to consider X/Twitter in the same way as other platforms, i.e., to continue using it if and only if we find enough interested volunteers.

The announcement that we are looking for volunteers (and possibly that we are leaving X/Twitter) would be made on the usual communication channels: Discourse (relayed to Zulip), Coq-Club, X/Twitter (where it could be the last post), and personal social media accounts of the team members (e.g., on Mastodon, LinkedIn) to increase reach.

After the volunteers are found and the list of platforms is finalized, we can create the accounts. The accounts can be created before the Rocq Prover renaming is finalized, but their owners should wait for the new visual identity and the go-ahead from the core team before starting to post.

If we depart from X/Twitter, the last post will remain pinned on the account, and the profile description will be updated to direct followers to the new platforms. In this case, there will be no need to update the visual identity or the name of the account.

We can also create a private Zulip channel for coordination between the social media team members.

The members of the social media team will be listed on the Rocq Prover website, and they will officially be part of the Rocq Prover team.

### Possible texts for the announcement

These are alternative texts that can be used for the announcement, with varying degrees of emphasis on the decision to leave X/Twitter and on the reasons for this decision.

#### Defending the decision to leave X/Twitter by incompatibility with the Rocq Prover values

> In the context of the upcoming renaming of Coq to the Rocq Prover, we are reconsidering which social media platforms to be present on. In particular, we intend to leave X/Twitter and to create accounts on other platforms, such as Mastodon, Bluesky or LinkedIn (although we are open to suggestions of which platforms to consider). We are looking for volunteers to help manage these accounts. If you are interested, please contact privately Théo Zimmermann on Zulip or by email.
>
> The decision to leave X/Twitter is motivated by the evolution of the moderation policies of the platform, which are no longer aligned with the values of the Rocq Prover project. In particular, the platform has been criticized for the proliferation of false information and conspiracy theories, and for the lack of respect for the European code of good conduct against misinformation. We consider that the platform is no fit for scientific communication and that it is not a place where we want to be present.

#### Defending the decision to leave X/Twitter by the evolution of the social media landscape and the death of academic Twitter

> In the context of the upcoming renaming of Coq to the Rocq Prover, we are reconsidering which social media platforms to be present on. In particular, we intend to leave X/Twitter and to create accounts on other platforms, such as Mastodon, Bluesky or LinkedIn (although we are open to suggestions of which platforms to consider). We are looking for volunteers to help manage these accounts. If you are interested, please contact privately Théo Zimmermann on Zulip or by email.
>
> The decision to leave X/Twitter is motivated by the evolution of the social media landscape. Many academics and academic institutions have left X/Twitter in the last years, and we consider that the platform is no longer the best place to reach our target audience.

#### Saying that X/Twitter will no longer be our "primary" social media platform without explicitly saying that we are leaving it

> In the context of the upcoming renaming of Coq to the Rocq Prover, we are reconsidering which social media platforms to be present on. In particular, we intend to create accounts on other platforms, such as Mastodon, Bluesky or LinkedIn (although we are open to suggestions of which platforms to consider). We are looking for volunteers to help manage these accounts. If you are interested, please contact privately Théo Zimmermann on Zulip or by email.
>
> The evolution of the social media landscape has led us to consider that X/Twitter can no longer be our primary social media platform. We are looking for new platforms where we can reach our target audience more effectively.

#### Saying that we are looking for volunteers to manage the social media accounts and that where we will be present will depend on where we find volunteers

> In the context of the upcoming renaming of Coq to the Rocq Prover, we are reconsidering our social media presence. We are looking for volunteers to help manage our social media accounts and for suggestions of which platforms to be present on. The future social media presence of the Rocq Prover will depend on where we find volunteers. If you are interested, please contact privately Théo Zimmermann on Zulip or by email.

## Drawbacks

- **Loss of reach and visibility:**
  Leaving X/Twitter may reduce the project's visibility and reach, especially in the short term. However, this is mitigated by the fact that the project's target audience is increasingly moving to other platforms. Experience from the NPR case is also interesting in this regard.

- **Risk of confusion between the messages of renaming and leaving X/Twitter:**
  Announcing the departure from X/Twitter at the same time as the renaming may confuse the community. However, the renaming was decided in particular because of the inclusivity issues that the previous name raised, and given the openness values that the project wants to promote, remaining on X/Twitter (or keeping X/Twitter as the primary social media presence of the Rocq prover) would be contradictory. Furthermore, the way the announcement is made can mitigate this risk by explaining the logic of reconsidering the social media presence in the context of the renaming.

## Alternatives

The "design" section already presents several possible paths, but here are some further alternatives:

- **Gradual Transition with Auto-Reposting**
  During a recent Coq Call, an alternative was proposed to maintain the X/Twitter account with auto-reposting from Mastodon and to archive it once the scientific community has largely left X.

  This approach has drawbacks, including: 
     - Continuing implicit endorsement of X/Twitter.
     - Requring to keep managing the account, including renaming it, monitoring replies and DMs.

- **Immediate Archiving Without Announcement**
  Another option is to quietly stop posting on X/Twitter without a formal announcement. However, this could be confusing if the CoqLang account still exists and is never renamed.

## Unresolved questions

- Which of the possible paths in the design section to choose and which announcement message to use.
- **Which platforms will be chosen for the Rocq Prover social media presence?** This is to be decided after the decision to leave X/Twitter is approved and motivated volunteers step forward.